module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeFunctorial
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamHorizontal

/-!
# Functoriality under composition of the base change map of completed de Rham complexes

`Crystalline.CompletedDeRham.baseChangeComplexHom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChange.lean` is the map
`α : M ⊗^∧_D Ω^*_D ⟶ M' ⊗^∧_{D'} Ω^*_{D'}` of completed de Rham complexes induced by a ring map
`D → D'` and a graded comparison `ψ` of forms.
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeFunctorial.lean` proves
what that map is along the *identity*, and proves functoriality under *composition* **in each
degree**; it does not assemble the composition law into a statement about the complexes.  This
module does.

## What was missing and is supplied here

Base changing along `D → D'` and then along `D' → D''` carries the module
`(M ⊗̂_D D') ⊗̂_{D'} D''`, whereas base changing along `D → D''` carries `M ⊗̂_D D''`.  So a
composition law has to be stated along a comparison of those two modules, which is
`Crystalline.CompletedConnection.baseChangeComposite`, and the degreewise law
`Crystalline.CompletedDeRham.baseChangeTerm_comp` holds along it.  What stopped that law from
being read on `CochainComplex AddCommGrpCat ℕ` is that the comparison was not known to be
**horizontal** for the two base-changed connections, hence not known to be a chain map.

It is horizontal, and that is the content of this module:
`Crystalline.CompletedConnection.baseChange_baseChangeComposite`.  With it the comparison
becomes a morphism of complexes through
`Crystalline.CompletedDeRham.horizontalComplexHom`, and the composition law is an identity of
morphisms of complexes, `Crystalline.CompletedDeRham.baseChangeComplexHom_comp`.

## How horizontality is proved

Two applications of the same reduction, and no level-by-level argument beyond it.  Both sides of
each identity are adically continuous additive maps out of a `p`-adic completion, so
`Crystalline.adicCompletion_addMonoidHom_ext` reduces the identity to the canonical image of the
uncompleted module, where additivity reduces it further to a pure tensor.

* On `M ⊗̂_D D'`, compared along `Crystalline.CompletedConnection.carrierMap`: the generator is
  `b' ⊗ m`, the `∇`-term is the already proved functoriality
  `Crystalline.CompletedConnection.baseChangeValues_comp` of the induced map on the values of a
  connection, and the Leibniz correction term matches because
  `ψ' (d' b') = d'' (b' mod D'')`.  This is
  `Crystalline.CompletedConnection.baseChange_carrierMap`.
* On `(M ⊗̂_D D') ⊗̂_{D'} D''`, compared along
  `Crystalline.CompletedConnection.baseChangeComposite`: the generator is `b'' ⊗ z`, the
  `∇`-term is the previous item, and the correction term matches because the comparison carries
  `1 ⊗ z` to `ρ z`.

The adic continuity of every map involved is recorded rather than re-derived each time:
`Crystalline.CompletedConnection.adicContinuous_baseChange` for a base-changed connection — its
value at level `pⁿ` is computed from the argument at level `pⁿ`, by
`Crystalline.CompletedConnection.baseChange_val` — and
`Crystalline.CompletedConnection.adicContinuous_baseChangeComposite` for the comparison, which
is the one map here that is not literally `Crystalline.adicCompletionMapₛₗ` of an uncompleted
map: it is that followed by the inverse of `AdicCompletion.of` on the `p`-adically complete
`M ⊗̂_D D''`, and the level-`pⁿ` estimate for the inverse is
`AdicCompletion.pow_smul_top_eq_ker_eval`, which holds because `(p)` is finitely generated.

## Where this is needed

`...SmallSite.computes07LH_of_computes07LG` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmoothPresentationDeRham.lean` carries `hab`, that
`β ≫ α = 𝟙`, as a hypothesis, and the functoriality of
`Crystalline.CompletedDeRham.baseChangeComplexHom` under composition — read on the complexes and
not only degreewise — is one of the three things its documentation records as owed.  The other
two are untouched here, and `hab` is **not** discharged: they are the identification of the
`Algebra` instances carried there with the maps `a`, `b` that
`Crystalline.exists_completedEnvelopeRetract` produces existentially, and the compatibility of
the hypothesis `gamma` — the direction `G ∘ F ≅ id` of the second assertion of
[Stacks, Lemma 60.17.5, Tag 07L5] — with the two base changes.  No `@[stacks …]` attribute is
placed anywhere in this module for
[Stacks, Tag 07LH]: nothing here is a statement of that tag.

## The retract of [Stacks, Lemma 60.17.5, Tag 07L5]

The composition law has one immediate consequence that *is* part of a tag, and it is the last
section of this module.  The proof of [Stacks, Lemma 60.17.5, Tag 07L5] derives one direction of
its second assertion from its first: "Since `a ∘ b = id_{D'}` we see that `F ∘ G` is the identity
functor."  With `D'' = D` and the composite `a ∘ b` the identity, the composition law identifies
the round trip of base changes with the base change along the identity, and
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_id` of
`CompletedConnectionBaseChangeFunctorial.lean` says that one is an isomorphism of complexes.
That is `Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract`, which carries
the [Stacks, Tag 07L5] attribute for that step.

For the opposite direction, `G ∘ F ≅ id`, the source reduces to the horizontality of the
comparison `c_{id_D, b ∘ a}` of the proof of [Stacks, Proposition 60.17.4, Tag 07JH] and then
says "It remains to prove that this map is horizontal, i.e., compatible with connections, which
we omit."  That horizontality is `Crystalline.nabla_taylorSum_eq` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorHorizontal.lean`; what still stands between it
and the equivalence of the two categories of pairs is set out in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean`, and the equivalence is claimed
nowhere here.

## Main definitions

Nothing is defined here; the comparisons this module is about are
`Crystalline.CompletedConnection.carrierMap` and
`Crystalline.CompletedConnection.baseChangeComposite` of
`CompletedConnectionBaseChangeFunctorial.lean`.

## Main results

* `Crystalline.CompletedConnection.baseChangeComposite_of_tmul` — the comparison on a pure
  tensor: `b'' ⊗ z ↦ b'' · ρ z`.
* `Crystalline.CompletedConnection.baseChangeComposite_baseChangeInclusion` — the comparison
  carries `1 ⊗ z` to the comparison `Crystalline.CompletedConnection.carrierMap` of `z`.
* `Crystalline.CompletedConnection.adicContinuous_baseChangeComposite`,
  `..._adicContinuous_baseChange`, `..._adicContinuous_carrierMap`,
  `..._adicContinuous_baseChangeValues` — adic continuity of the four maps the reduction
  composes.
* `Crystalline.CompletedConnection.compatible_of_comp` — the compatibility
  `ψ_comp (d x) = d'' (x mod D'')` of the composed comparison of forms with the composed
  differential is a consequence of the two it is composed from.
* `Crystalline.CompletedConnection.baseChange_carrierMap` — **horizontality of the comparison
  `M ⊗̂_D D' → M ⊗̂_D D''`.**
* `Crystalline.CompletedConnection.baseChange_baseChangeComposite` — **horizontality of the
  comparison `(M ⊗̂_D D') ⊗̂_{D'} D'' → M ⊗̂_D D''`**, which is what makes it a chain map.
* `Crystalline.CompletedDeRham.horizontalTerm_baseChangeComposite` — the degree-`i` component of
  the induced morphism of complexes is
  `Crystalline.CompletedConnection.baseChangeValuesComposite`, the two being the same map
  written in Mathlib's `AdicCompletion.map` shape and in the
  `Crystalline.adicCompletionMapₛₗ` shape.
* `Crystalline.CompletedDeRham.wedge_of_comp` and `Crystalline.CompletedDeRham.deRham_of_comp` —
  the two compatibilities of the composed comparison of forms are consequences of those of the
  factors, so the composition law assumes nothing of `ψ_comp` that `ψ` and `ψ'` do not already
  give.
* `Crystalline.CompletedDeRham.baseChangeComplexHom_comp` — **functoriality under composition as
  an identity of morphisms of complexes**, `α_ψ ≫ α_{ψ'} ≫ ρ = α_{ψ_comp}`.
* `Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract` — **the round trip of
  base changes along a retract `a ∘ b = id` of rings is an isomorphism of completed de Rham
  complexes**, which is the step of the second assertion of [Stacks, Lemma 60.17.5, Tag 07L5]
  that its proof derives from the first.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u v v' v'' w

namespace Crystalline

namespace CompletedConnection

section Composite

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type w) [AddCommGroup M] [Module D M]

/-- **The comparison on a pure tensor**: `b'' ⊗ z ↦ b'' · ρ z`. -/
public theorem baseChangeComposite_of_tmul (b'' : D'') (z : baseChangeCarrier p D D' M) :
    baseChangeComposite p D D' D'' M
        (AdicCompletion.of (pAdicIdeal (A := D'') p)
          (D'' ⊗[D'] baseChangeCarrier p D D' M) (b'' ⊗ₜ[D'] z)) =
      b'' • carrierMap p D D' D'' M z := by
  let : IsAdicComplete (pAdicIdeal (A := D'') p) (baseChangeCarrier p D D'' M) :=
    isPAdicallyComplete_baseChangeCarrier p D D'' M
  show (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p)
      (baseChangeCarrier p D D'' M)).symm
      (adicCompletionMapLinear ((carrierMapLinear p D D' D'' M).liftBaseChange D'')
        (pAdicIdeal (A := D'') p)
        (AdicCompletion.of _ _ (b'' ⊗ₜ[D'] z))) = _
  rw [adicCompletionMapLinear_of, AdicCompletion.ofLinearEquiv_symm_of,
    LinearMap.liftBaseChange_tmul, carrierMapLinear_apply]

/-- **The comparison carries the inclusion `z ↦ 1 ⊗ z` to the comparison of base-changed
modules**: `ρ` of `1 ⊗ z` is the image of `z` under `M ⊗̂_D D' → M ⊗̂_D D''`. -/
public theorem baseChangeComposite_baseChangeInclusion (z : baseChangeCarrier p D D' M) :
    baseChangeComposite p D D' D'' M
        (baseChangeInclusion p D' D'' (baseChangeCarrier p D D' M) z) =
      carrierMap p D D' D'' M z := by
  rw [baseChangeInclusion_apply, baseChangeComposite_of_tmul, one_smul]

/-- A completion element whose image under the canonical map into the *double* completion dies at
level `pⁿ` dies there itself. -/
private theorem eval_eq_zero_of_eval_of_eq_zero {R : Type u} [CommRing R] {X : Type w}
    [AddCommGroup X] [Module R X] (I : Ideal R) (hfg : I.FG) (n : ℕ)
    {v : AdicCompletion I X}
    (h : AdicCompletion.eval I (AdicCompletion I X) n
      (AdicCompletion.of I (AdicCompletion I X) v) = 0) :
    AdicCompletion.eval I X n v = 0 := by
  rw [AdicCompletion.eval_of] at h
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hfg]
  simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h

/-- **The comparison of the twice base-changed module with the once base-changed one is adically
continuous**: it does not lower the level at which an element is known. -/
public theorem adicContinuous_baseChangeComposite :
    SemilinearCosimplicialModule.AdicContinuous (pAdicIdeal (A := D'') p)
      (pAdicIdeal (A := D'') p) (baseChangeComposite p D D' D'' M) := by
  let : IsAdicComplete (pAdicIdeal (A := D'') p) (baseChangeCarrier p D D'' M) :=
    isPAdicallyComplete_baseChangeCarrier p D D'' M
  intro n
  refine ⟨n, fun x hx ↦ ?_⟩
  refine eval_eq_zero_of_eval_of_eq_zero (pAdicIdeal (A := D'') p) (pAdicIdeal_fg p D'') n ?_
  have hof : AdicCompletion.of (pAdicIdeal (A := D'') p) (baseChangeCarrier p D D'' M)
      (baseChangeComposite p D D' D'' M x) =
      adicCompletionMapLinear ((carrierMapLinear p D D' D'' M).liftBaseChange D'')
        (pAdicIdeal (A := D'') p) x :=
    AdicCompletion.of_ofLinearEquiv_symm _ _
  rw [hof]
  show adicQuotientMap ((carrierMapLinear p D D' D'' M).liftBaseChange D'')
    (le_of_eq (Ideal.map_id _)) n (x.val n) = 0
  rw [show x.val n = 0 from hx, map_zero]

end Composite

/-! ### Adic continuity of a base-changed connection -/

section Continuity

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type w) [AddCommGroup M] [Module D M]
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  (Omega' : Type v') [AddCommGroup Omega'] [Module D' Omega']
  (d' : D' → Omega') (psi : Omega →ₛₗ[algebraMap D D'] Omega')
  {d : D → Omega} (nabla : CompletedConnection p D Omega d M)
  (hadd' : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hleib' : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi : ∀ x : D, psi (d x) = d' (algebraMap D D' x))

/-- **A base-changed connection is adically continuous**, and with no loss of level: its value at
level `pⁿ` is computed from the argument at level `pⁿ`, by
`Crystalline.CompletedConnection.baseChange_val`. -/
public theorem adicContinuous_baseChange :
    SemilinearCosimplicialModule.AdicContinuous (pAdicIdeal (A := D') p)
      (pAdicIdeal (A := D') p)
      (baseChange p D D' M Omega Omega' d' psi nabla hadd' hleib' hpsi) := by
  intro n
  refine ⟨n, fun x hx ↦ ?_⟩
  show (baseChange p D D' M Omega Omega' d' psi nabla hadd' hleib' hpsi x).val n = 0
  rw [baseChange_val, show x.val n = 0 from hx, map_zero]

/-- **The comparison of base-changed modules along `D' → D''` is adically continuous**: it is
`Crystalline.adicCompletionMapₛₗ` of a map of uncompleted modules. -/
public theorem adicContinuous_carrierMap (D'' : Type u) [CommRing D''] [Algebra D' D'']
    [Algebra D D''] [IsScalarTower D D' D''] :
    SemilinearCosimplicialModule.AdicContinuous (pAdicIdeal (A := D') p)
      (pAdicIdeal (A := D'') p) (carrierMap p D D' D'' M) :=
  adicCompletionMapₛₗ_continuous _ _

/-- **The map induced on the values of a connection is adically continuous**, being
`Crystalline.adicCompletionMapₛₗ` of `Crystalline.CompletedConnection.baseChangeTensor`. -/
public theorem adicContinuous_baseChangeValues :
    SemilinearCosimplicialModule.AdicContinuous (pAdicIdeal (A := D) p)
      (pAdicIdeal (A := D') p)
      (baseChangeValues p D D' M Omega Omega' psi) :=
  adicCompletionMapₛₗ_continuous _ _

end Continuity

/-! ### Horizontality of the comparison of the twice base-changed module -/

/-- Two additive adically continuous maps out of the completion of `A ⊗[B] N` agree as soon as
they agree on the image of each pure tensor. -/
private theorem eq_of_forall_of_tmul {A B N T Q : Type*} [CommRing A] [CommRing B] [Algebra B A]
    [AddCommGroup N] [Module B N] [CommRing T] [AddCommGroup Q] [Module T Q] {I : Ideal A}
    {J : Ideal T} (f g : AdicCompletion I (A ⊗[B] N) → AdicCompletion J Q)
    (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (hfc : SemilinearCosimplicialModule.AdicContinuous I J f)
    (hgc : SemilinearCosimplicialModule.AdicContinuous I J g)
    (h : ∀ (a : A) (n : N),
      f (AdicCompletion.of I _ (a ⊗ₜ[B] n)) = g (AdicCompletion.of I _ (a ⊗ₜ[B] n)))
    (z : AdicCompletion I (A ⊗[B] N)) : f z = g z := by
  let F := AddMonoidHom.mk' f hf
  let G := AddMonoidHom.mk' g hg
  have hgen : ∀ y, F (AdicCompletion.of I _ y) = G (AdicCompletion.of I _ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [_root_.map_zero, _root_.map_zero, _root_.map_zero]
    | tmul a n => exact h a n
    | add a b ha hb => rw [_root_.map_add, _root_.map_add, _root_.map_add, ha, hb]
  exact DFunLike.congr_fun (adicCompletion_addMonoidHom_ext hfc hgc hgen) z

section CompositeConnection

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type w) [AddCommGroup M] [Module D M]
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  (Omega' : Type v') [AddCommGroup Omega'] [Module D' Omega']
  (Omega'' : Type v'') [AddCommGroup Omega''] [Module D'' Omega'']
  {d : D → Omega} (d' : D' → Omega') (d'' : D'' → Omega'')
  (psi : Omega →ₛₗ[algebraMap D D'] Omega')
  (psi' : Omega' →ₛₗ[algebraMap D' D''] Omega'')
  (psiComp : Omega →ₛₗ[algebraMap D D''] Omega'')
  (nabla : CompletedConnection p D Omega d M)
  (hadd' : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hleib' : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi : ∀ x : D, psi (d x) = d' (algebraMap D D' x))
  (hadd'' : ∀ x y : D'', d'' (x + y) = d'' x + d'' y)
  (hleib'' : ∀ x y : D'', d'' (x * y) = x • d'' y + y • d'' x)
  (hpsi' : ∀ x : D', psi' (d' x) = d'' (algebraMap D' D'' x))
  (hpsiComp : ∀ omega : Omega, psiComp omega = psi' (psi omega))

include hpsi hpsi' hpsiComp in
/-- **The composed comparison of forms is compatible with the composed differential**: from
`ψ (d x) = d' (a x)` and `ψ' (d' y) = d'' (c y)` and `ψ_comp = ψ' ∘ ψ` it follows that
`ψ_comp (d x) = d'' (x mod D'')`.  This is the third hypothesis the base change along
`D → D''` needs, and it is a consequence of the two it is composed from, not a further
assumption. -/
public theorem compatible_of_comp (x : D) : psiComp (d x) = d'' (algebraMap D D'' x) := by
  rw [hpsiComp, hpsi, hpsi', ← IsScalarTower.algebraMap_apply]

variable (hder'' : ∀ x : D, psiComp (d x) = d'' (algebraMap D D'' x))

include hpsiComp hpsi' in
/-- **Horizontality of the comparison `M ⊗̂_D D' → M ⊗̂_D D''` of base-changed modules.**  The
connection base changed along `D → D''` and the connection base changed along `D → D'`, pushed
forward along `D' → D''`, agree along the comparison
`Crystalline.CompletedConnection.carrierMap` of the two modules.

Both sides are adically continuous additive maps out of the completion `M ⊗̂_D D'`, so
`Crystalline.adicCompletion_addMonoidHom_ext` reduces the identity to the image of the
uncompleted `D' ⊗[D] M`, where it is checked on a pure tensor `b' ⊗ m`.  There it is the sum of
two statements: on the `∇`-term it is functoriality of the induced map on the values of a
connection, `Crystalline.CompletedConnection.baseChangeValues_comp`, and on the Leibniz
correction term it is the compatibility `ψ' (d' b') = d'' (b' mod D'')`. -/
public theorem baseChange_carrierMap (z : baseChangeCarrier p D D' M) :
    baseChange p D D'' M Omega Omega'' d'' psiComp nabla hadd'' hleib'' hder''
        (carrierMap p D D' D'' M z) =
      baseChangeValuesComposite p D D' D'' M Omega''
        (baseChangeValues p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi'
          (baseChange p D D' M Omega Omega' d' psi nabla hadd' hleib' hpsi z)) := by
  set nablaBar := baseChange p D D'' M Omega Omega'' d'' psiComp nabla hadd'' hleib'' hder''
    with hnablaBar
  set nablaOne := baseChange p D D' M Omega Omega' d' psi nabla hadd' hleib' hpsi with hnablaOne
  refine eq_of_forall_of_tmul (A := D') (B := D) (N := M)
    (fun w ↦ nablaBar (carrierMap p D D' D'' M w))
    (fun w ↦ baseChangeValuesComposite p D D' D'' M Omega''
      (baseChangeValues p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi' (nablaOne w)))
    (fun x y ↦ by rw [_root_.map_add, nablaBar.map_add])
    (fun x y ↦ by rw [nablaOne.map_add, _root_.map_add, _root_.map_add])
    (adicContinuous_of_comp (adicContinuous_carrierMap p D D' M D'')
      (adicContinuous_baseChange p D D'' M Omega Omega'' d'' psiComp nabla hadd'' hleib'' hder'')
      (fun _ ↦ rfl))
    (adicContinuous_of_comp
      (adicContinuous_of_comp
        (adicContinuous_baseChange p D D' M Omega Omega' d' psi nabla hadd' hleib' hpsi)
        (adicContinuous_baseChangeValues p D' D'' (baseChangeCarrier p D D' M) Omega' Omega''
          psi') (fun _ ↦ rfl))
      (adicCompletionMapLinear_continuous _ _) (fun _ ↦ rfl))
    (fun b' m ↦ ?_) z
  rw [carrierMap_of, carrierTensorMap_tmul,
    of_tmul_eq_smul_inclusion p D D'' M (algebraMap D' D'' b') m, hnablaBar,
    baseChange_smul, baseChange_inclusion, hnablaOne, baseChange_of_tmul,
    _root_.map_add, LinearMap.map_smulₛₗ, correction_apply,
    baseChangeValues_of_tmul p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi',
    _root_.map_add, _root_.map_smul,
    baseChangeValues_comp p D D' D'' M Omega Omega' Omega'' psi psi' psiComp hpsiComp,
    hpsi' b', baseChangeValuesComposite, adicCompletionMapLinear_of,
    LinearMap.rTensor_tmul, baseChangeComposite_inclusion]

include hpsiComp hpsi' in
/-- **The comparison of the twice base-changed module with the once base-changed one is
horizontal**, hence a morphism of modules with connection: the connection base changed along
`D → D''` and the connection base changed along `D → D'` and then along `D' → D''` agree along
`Crystalline.CompletedConnection.baseChangeComposite`.

This is the input that lets the degreewise functoriality
`Crystalline.CompletedDeRham.baseChangeTerm_comp` be read on the complexes themselves, which it
could not be while the comparison was not known to be a chain map; see
`Crystalline.CompletedDeRham.baseChangeComplexHom_comp`.

The proof is the same reduction as for
`Crystalline.CompletedConnection.baseChange_carrierMap`: both sides are adically continuous
additive maps out of a completion, so the identity reduces to a pure tensor `b'' ⊗ z` of
`D'' ⊗[D'] (M ⊗̂_D D')`, where the `∇`-term is that lemma and the Leibniz correction term matches
because the comparison carries `1 ⊗ z` to `ρ z`. -/
public theorem baseChange_baseChangeComposite
    (x : baseChangeCarrier p D' D'' (baseChangeCarrier p D D' M)) :
    baseChange p D D'' M Omega Omega'' d'' psiComp nabla hadd'' hleib'' hder''
        (baseChangeComposite p D D' D'' M x) =
      baseChangeValuesComposite p D D' D'' M Omega''
        (baseChange p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' d'' psi'
          (baseChange p D D' M Omega Omega' d' psi nabla hadd' hleib' hpsi) hadd'' hleib''
          hpsi' x) := by
  set nablaBar := baseChange p D D'' M Omega Omega'' d'' psiComp nabla hadd'' hleib'' hder''
    with hnablaBar
  set nablaOne := baseChange p D D' M Omega Omega' d' psi nabla hadd' hleib' hpsi with hnablaOne
  set nablaTwo := baseChange p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' d'' psi'
    nablaOne hadd'' hleib'' hpsi' with hnablaTwo
  refine eq_of_forall_of_tmul (A := D'') (B := D') (N := baseChangeCarrier p D D' M)
    (fun w ↦ nablaBar (baseChangeComposite p D D' D'' M w))
    (fun w ↦ baseChangeValuesComposite p D D' D'' M Omega'' (nablaTwo w))
    (fun a b ↦ by rw [_root_.map_add, nablaBar.map_add])
    (fun a b ↦ by rw [nablaTwo.map_add, _root_.map_add])
    (adicContinuous_of_comp (adicContinuous_baseChangeComposite p D D' D'' M)
      (adicContinuous_baseChange p D D'' M Omega Omega'' d'' psiComp nabla hadd'' hleib'' hder'')
      (fun _ ↦ rfl))
    (adicContinuous_of_comp
      (adicContinuous_baseChange p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' d'' psi'
        nablaOne hadd'' hleib'' hpsi')
      (adicCompletionMapLinear_continuous _ _) (fun _ ↦ rfl))
    (fun b'' z ↦ ?_) x
  rw [baseChangeComposite_of_tmul, hnablaBar, baseChange_smul,
    baseChange_carrierMap p D D' D'' M Omega Omega' Omega'' d' d'' psi psi' psiComp nabla
      hadd' hleib' hpsi hadd'' hleib'' hpsi' hpsiComp hder'',
    hnablaTwo, baseChange_of_tmul, _root_.map_add, _root_.map_smul, ← hnablaOne,
    correction_apply, baseChangeValuesComposite, adicCompletionMapLinear_of,
    LinearMap.rTensor_tmul, baseChangeComposite_baseChangeInclusion]

end CompositeConnection

end CompletedConnection

/-! ### The composition law on the complexes -/

namespace CompletedDeRham

section CompositeComplex

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (Om'' : ℕ → Type u) [∀ i, AddCommGroup (Om'' i)] [∀ i, Module D'' (Om'' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (psi' : ∀ i, Om' i →ₛₗ[algebraMap D' D''] Om'' i)
  (psiComp : ∀ i, Om i →ₛₗ[algebraMap D D''] Om'' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (wedge'' : ∀ i, Om'' i →ₗ[D''] Om'' 1 →ₗ[D''] Om'' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  (deRham'' : ∀ i, Om'' i →+ Om'' (i + 1))

/-- **The degree-`i` comparison of the twice base-changed complex with the once base-changed
one is the comparison of `Crystalline.CompletedConnection.baseChangeComposite` read on the
completed tensor products.**  The two are the same map written two ways: Mathlib's
`AdicCompletion.map` of `e ⊗ 1`, which is the shape
`Crystalline.CompletedDeRham.horizontalTerm` is built in, and
`Crystalline.adicCompletionMapₛₗ` of the same map, which is the shape
`Crystalline.CompletedConnection.baseChangeValuesComposite` is built in. -/
public theorem horizontalTerm_baseChangeComposite (i : ℕ)
    (z : CompletedTensor p D'' (Om'' i)
      (CompletedConnection.baseChangeCarrier p D' D''
        (CompletedConnection.baseChangeCarrier p D D' M))) :
    horizontalTerm p D''
        (CompletedConnection.baseChangeCarrier p D' D''
          (CompletedConnection.baseChangeCarrier p D D' M))
        (CompletedConnection.baseChangeCarrier p D D'' M) Om''
        (CompletedConnection.baseChangeComposite p D D' D'' M) i z =
      CompletedConnection.baseChangeValuesComposite p D D' D'' M (Om'' i) z :=
  adicCompletionMap_eq_mapₛₗ _ _ z

variable (hpsiComp : ∀ (i : ℕ) (omega : Om i), psiComp i omega = psi' i (psi i omega))

omit [IsScalarTower D D' D''] in
include hpsiComp in
/-- **The composed comparison of forms is multiplicative for the wedge product**, given that each
of the two factors is.  So the hypothesis `hpsi_wedge` of the base change along `D → D''` is a
consequence of the two it is composed from. -/
public theorem wedge_of_comp
    (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
      psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
    (hpsi'_wedge : ∀ (i : ℕ) (omega : Om' i) (eta : Om' 1),
      psi' (i + 1) (wedge' i omega eta) = wedge'' i (psi' i omega) (psi' 1 eta))
    (i : ℕ) (omega : Om i) (eta : Om 1) :
    psiComp (i + 1) (wedge i omega eta) =
      wedge'' i (psiComp i omega) (psiComp 1 eta) := by
  rw [hpsiComp, hpsi_wedge, hpsi'_wedge, hpsiComp, hpsiComp]

omit [IsScalarTower D D' D''] in
include hpsiComp in
/-- **The composed comparison of forms commutes with the de Rham differential**, given that each
of the two factors does. -/
public theorem deRham_of_comp
    (hpsi_deRham : ∀ (i : ℕ) (omega : Om i), psi (i + 1) (deRham i omega) = deRham' i (psi i omega))
    (hpsi'_deRham : ∀ (i : ℕ) (omega : Om' i),
      psi' (i + 1) (deRham' i omega) = deRham'' i (psi' i omega))
    (i : ℕ) (omega : Om i) :
    psiComp (i + 1) (deRham i omega) = deRham'' i (psiComp i omega) := by
  rw [hpsiComp, hpsi_deRham, hpsi'_deRham, hpsiComp]

variable {d : D → Om 1} (d' : D' → Om' 1) (d'' : D'' → Om'' 1)
  (nabla : CompletedConnection p D (Om 1) d M)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hd''add : ∀ x y : D'', d'' (x + y) = d'' x + d'' y)
  (hd''leib : ∀ x y : D'', d'' (x * y) = x • d'' y + y • d'' x)
  (hpsi'1 : ∀ x : D', psi' 1 (d' x) = d'' (algebraMap D' D'' x))
  (hpsiComp1 : ∀ x : D, psiComp 1 (d x) = d'' (algebraMap D D'' x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hleib'' : IsGradedLeibniz D'' Om'' wedge'' deRham'' d'')
  (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
  (hpsi_deRham : ∀ (i : ℕ) (omega : Om i), psi (i + 1) (deRham i omega) = deRham' i (psi i omega))
  (hpsi'_wedge : ∀ (i : ℕ) (omega : Om' i) (eta : Om' 1),
    psi' (i + 1) (wedge' i omega eta) = wedge'' i (psi' i omega) (psi' 1 eta))
  (hpsi'_deRham : ∀ (i : ℕ) (omega : Om' i),
    psi' (i + 1) (deRham' i omega) = deRham'' i (psi' i omega))
  (hpsiComp_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psiComp (i + 1) (wedge i omega eta) = wedge'' i (psiComp i omega) (psiComp 1 eta))
  (hpsiComp_deRham : ∀ (i : ℕ) (omega : Om i),
    psiComp (i + 1) (deRham i omega) = deRham'' i (psiComp i omega))

include hpsiComp hpsi'1 hpsiComp1 in
/-- **Functoriality of the base change map of completed de Rham complexes under composition, as
an identity of morphisms of complexes.**

Base changing the complex `M ⊗^∧_D Ω^*_D` along `D → D'` and then along `D' → D''` is base
changing it along `D → D''`, once the twice base-changed complex is compared with the once base
changed one by the horizontal map
`Crystalline.CompletedConnection.baseChangeComposite`:

`α_ψ ≫ α_{ψ'} ≫ ρ = α_{ψ_comp}`.

This is the composition half of the functoriality that `hab` of
`...SmallSite.computes07LH_of_computes07LG` needs, and the thing
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeFunctorial.lean` left
undone: the degreewise law `Crystalline.CompletedDeRham.baseChangeTerm_comp` was available there,
but the comparison it is stated along was not known to be a chain map, so the law could not be
read on `CochainComplex AddCommGrpCat ℕ`.  It is a chain map now, by
`Crystalline.CompletedConnection.baseChange_baseChangeComposite`.

The identity itself is degreewise: a morphism of complexes is determined by its components, and
in degree `i` the composite is `Crystalline.CompletedDeRham.baseChangeTerm_comp`. -/
public theorem baseChangeComplexHom_comp
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : IsSquareZero p D' Om' wedge' deRham'
      (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
        hpsi1) hleib')
    (hsq'' : IsSquareZero p D'' Om'' wedge'' deRham''
      (CompletedConnection.baseChangeCarrier p D' D''
        (CompletedConnection.baseChangeCarrier p D D' M))
      (CompletedConnection.baseChange p D' D''
        (CompletedConnection.baseChangeCarrier p D D' M) (Om' 1) (Om'' 1) d'' (psi' 1)
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) hd''add hd''leib hpsi'1) hleib'')
    (hsqBar : IsSquareZero p D'' Om'' wedge'' deRham''
      (CompletedConnection.baseChangeCarrier p D D'' M)
      (CompletedConnection.baseChange p D D'' M (Om 1) (Om'' 1) d'' (psiComp 1) nabla hd''add
        hd''leib hpsiComp1) hleib'') :
    baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla hd'add
          hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq' ≫
        (baseChangeComplexHom p D' D''
            (CompletedConnection.baseChangeCarrier p D D' M) Om' Om'' psi' wedge' wedge''
            deRham' deRham'' d''
            (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
              hd'leib hpsi1) hd''add hd''leib hpsi'1 hleib' hleib'' hpsi'_wedge hpsi'_deRham
            hsq' hsq'' ≫
          horizontalComplexHom p D''
            (CompletedConnection.baseChangeCarrier p D' D''
              (CompletedConnection.baseChangeCarrier p D D' M))
            (CompletedConnection.baseChangeCarrier p D D'' M) Om''
            (CompletedConnection.baseChangeComposite p D D' D'' M) wedge'' deRham''
            (CompletedConnection.baseChange p D' D''
              (CompletedConnection.baseChangeCarrier p D D' M) (Om' 1) (Om'' 1) d'' (psi' 1)
              (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
                hd'leib hpsi1) hd''add hd''leib hpsi'1)
            (CompletedConnection.baseChange p D D'' M (Om 1) (Om'' 1) d'' (psiComp 1) nabla
              hd''add hd''leib hpsiComp1) hleib''
            (CompletedConnection.baseChange_baseChangeComposite p D D' D'' M (Om 1) (Om' 1)
              (Om'' 1) d' d'' (psi 1) (psi' 1) (psiComp 1) nabla hd'add hd'leib hpsi1 hd''add
              hd''leib hpsi'1 (hpsiComp 1) hpsiComp1)
            hsq'' hsqBar) =
      baseChangeComplexHom p D D'' M Om Om'' psiComp wedge wedge'' deRham deRham'' d'' nabla
        hd''add hd''leib hpsiComp1 hleib hleib'' hpsiComp_wedge hpsiComp_deRham hsq hsqBar := by
  refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  refine AddCommGrpCat.ext fun x ↦ ?_
  show horizontalTerm p D''
      (CompletedConnection.baseChangeCarrier p D' D''
        (CompletedConnection.baseChangeCarrier p D D' M))
      (CompletedConnection.baseChangeCarrier p D D'' M) Om''
      (CompletedConnection.baseChangeComposite p D D' D'' M) i
      (baseChangeTerm p D' D'' (CompletedConnection.baseChangeCarrier p D D' M) Om' Om'' psi' i
        (baseChangeTerm p D D' M Om Om' psi i x)) =
    baseChangeTerm p D D'' M Om Om'' psiComp i x
  rw [horizontalTerm_baseChangeComposite]
  exact baseChangeTerm_comp p D D' D'' M Om Om' Om'' psi psi' psiComp hpsiComp i x

end CompositeComplex

/-! ### The base change along a retract of rings -/

section RetractComplex

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  [Algebra D' D] [IsScalarTower D D' D] (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (psi' : ∀ i, Om' i →ₛₗ[algebraMap D' D] Om i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) (nabla : CompletedConnection p D (Om 1) d M)
  (hdadd : ∀ x y : D, d (x + y) = d x + d y)
  (hdleib : ∀ x y : D, d (x * y) = x • d y + y • d x)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hpsi'1 : ∀ x : D', psi' 1 (d' x) = d (algebraMap D' D x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
  (hpsi_deRham : ∀ (i : ℕ) (omega : Om i),
    psi (i + 1) (deRham i omega) = deRham' i (psi i omega))
  (hpsi'_wedge : ∀ (i : ℕ) (omega : Om' i) (eta : Om' 1),
    psi' (i + 1) (wedge' i omega eta) = wedge i (psi' i omega) (psi' 1 eta))
  (hpsi'_deRham : ∀ (i : ℕ) (omega : Om' i),
    psi' (i + 1) (deRham' i omega) = deRham i (psi' i omega))
  (hretract : ∀ (i : ℕ) (omega : Om i), psi' i (psi i omega) = omega)

include hdadd hdleib hd'add hd'leib hpsi1 hpsi'1 hleib hleib' hpsi_wedge hpsi_deRham
  hpsi'_wedge hpsi'_deRham hretract in
/-- **The round trip of base changes along a retract of rings is an isomorphism of completed de
Rham complexes.**

Let `b : D → D'` and `a : D' → D` be ring maps with `a ∘ b = id_D` — that is the instance
`IsScalarTower D D' D`, since `algebraMap D D` is the identity — and let the graded comparisons
of forms `ψ` along `b` and `ψ'` along `a` satisfy `ψ' ∘ ψ = id` likewise.  Then base changing
the completed de Rham complex of `(M, ∇)` along `b` and then along `a`, and comparing the twice
base-changed module with the once base-changed one by
`Crystalline.CompletedConnection.baseChangeComposite`, gives an isomorphism of complexes.

This is the step of the second assertion of [Stacks, Lemma 60.17.5, Tag 07L5] that the source's
proof derives from the first: "Since `a ∘ b = id_{D'}` we see that `F ∘ G` is the identity
functor", read on the completed de Rham complexes rather than on the pairs themselves.  The
naming here is the source's with `D` and `D'` interchanged: the module `M` of this statement
lives over the ring the source calls `D'`, which is the ring `G` base changes *away from* and
`F` base changes back *to*.

The proof is the two halves of the functoriality put together, with nothing further assumed:
the composition law `Crystalline.CompletedDeRham.baseChangeComplexHom_comp` identifies the round
trip with the base change along the composite `a ∘ b`, and the composite is the identity, where
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_id` applies — that lemma needing exactly
the `p`-adic completeness of `M`, which is [Stacks, Tag 07JB] and one of the four conditions a
`Crystalline.Pair` carries.

The other direction, `G ∘ F ≅ id`, is the one whose last step the source's own proof leaves to
the reader: there it produces the comparison `c_{id_D, b ∘ a}` of modules from the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] and then says of its compatibility with the connections
"It remains to prove that this map is horizontal, i.e., compatible with connections, which we
omit."  That horizontality is `Crystalline.nabla_taylorSum_eq` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorHorizontal.lean`; the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean` says what the equivalence of the
two categories of pairs asks for beyond it.  This theorem concludes the first direction. -/
public theorem isIso_baseChangeComplexHom_comp_of_retract
    (hM : IsPAdicallyComplete p D M)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : IsSquareZero p D' Om' wedge' deRham'
      (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
        hpsi1) hleib')
    (hsq'' : IsSquareZero p D Om wedge deRham
      (CompletedConnection.baseChangeCarrier p D' D
        (CompletedConnection.baseChangeCarrier p D D' M))
      (CompletedConnection.baseChange p D' D
        (CompletedConnection.baseChangeCarrier p D D' M) (Om' 1) (Om 1) d (psi' 1)
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) hdadd hdleib hpsi'1) hleib)
    (hsqId : IsSquareZero p D Om wedge deRham
      (CompletedConnection.baseChangeCarrier p D D M)
      (CompletedConnection.baseChange p D D M (Om 1) (Om 1) d LinearMap.id nabla hdadd hdleib
        (fun _ ↦ rfl)) hleib) :
    IsIso (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla
          hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq' ≫
        (baseChangeComplexHom p D' D (CompletedConnection.baseChangeCarrier p D D' M) Om' Om
            psi' wedge' wedge deRham' deRham d
            (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
              hd'leib hpsi1) hdadd hdleib hpsi'1 hleib' hleib hpsi'_wedge hpsi'_deRham
            hsq' hsq'' ≫
          horizontalComplexHom p D
            (CompletedConnection.baseChangeCarrier p D' D
              (CompletedConnection.baseChangeCarrier p D D' M))
            (CompletedConnection.baseChangeCarrier p D D M) Om
            (CompletedConnection.baseChangeComposite p D D' D M) wedge deRham
            (CompletedConnection.baseChange p D' D
              (CompletedConnection.baseChangeCarrier p D D' M) (Om' 1) (Om 1) d (psi' 1)
              (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
                hd'leib hpsi1) hdadd hdleib hpsi'1)
            (CompletedConnection.baseChange p D D M (Om 1) (Om 1) d LinearMap.id nabla hdadd
              hdleib (fun _ ↦ rfl)) hleib
            (CompletedConnection.baseChange_baseChangeComposite p D D' D M (Om 1) (Om' 1)
              (Om 1) d' d (psi 1) (psi' 1) LinearMap.id nabla hd'add hd'leib hpsi1 hdadd
              hdleib hpsi'1 (fun omega ↦ (hretract 1 omega).symm) (fun _ ↦ rfl))
            hsq'' hsqId)) := by
  rw [baseChangeComplexHom_comp (p := p) (D := D) (D' := D') (D'' := D) (M := M) (Om := Om)
    (Om' := Om') (Om'' := Om) (psi := psi) (psi' := psi') (psiComp := fun _ ↦ LinearMap.id)
    (wedge := wedge) (wedge' := wedge') (wedge'' := wedge) (deRham := deRham)
    (deRham' := deRham') (deRham'' := deRham) (d := d) (d' := d') (d'' := d) (nabla := nabla)
    (hd'add := hd'add) (hd'leib := hd'leib) (hpsi1 := hpsi1) (hd''add := hdadd)
    (hd''leib := hdleib) (hpsi'1 := hpsi'1) (hpsiComp1 := fun _ ↦ rfl) (hleib := hleib)
    (hleib' := hleib') (hleib'' := hleib) (hpsi_wedge := hpsi_wedge)
    (hpsi_deRham := hpsi_deRham) (hpsi'_wedge := hpsi'_wedge) (hpsi'_deRham := hpsi'_deRham)
    (hpsiComp_wedge := fun _ _ _ ↦ rfl) (hpsiComp_deRham := fun _ _ ↦ rfl)
    (hpsiComp := fun i omega ↦ (hretract i omega).symm) (hsq := hsq) (hsq' := hsq')
    (hsq'' := hsq'') (hsqBar := hsqId)]
  exact isIso_baseChangeComplexHom_id p D M Om wedge deRham nabla hdadd hdleib hleib hM hsq hsqId

end RetractComplex

end CompletedDeRham

end Crystalline

end
