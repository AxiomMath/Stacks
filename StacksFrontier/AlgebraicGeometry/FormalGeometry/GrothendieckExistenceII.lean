module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AnnihilatorSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Algebraize
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AlgebraizationUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ClosedPushforward
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.IdealPowerQuotientTower
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LiftedQuotientAdicSystem
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LiftedQuotientRow
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LiftedQuotientTower
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LiftedQuotientTowerMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackEquivalence
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TwoIdealAdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete

/-!
# Grothendieck's existence theorem, II: the two-ideal algebraization criterion

Let `X` be a Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves, let `X_e ⊆ X`
be the closed subscheme cut out by `𝒦 ᵉ` and let `ℐ_e = ℐ 𝒪_{X_e}`. Tag 088A says that an object
`(F_n)` of `Coh(X, ℐ)` is in the essential image of the completion functor of Tag 0880 as soon as

1. the functor `Coh(𝒪_{X_e}) ⟶ Coh(X_e, ℐ_e)` is an equivalence for every `e ≥ 1`, and
2. there is a coherent `𝒪_X`-module `H` and a map `α : (F_n) ⟶ H ^∧` whose kernel and cokernel
   are annihilated by a power of `𝒦`.

This file carries the lemma itself, together with the seven parts of the source's proof that
are assembled into it here.

The first is the opening move of the source's proof: dividing every term of `(F_n)` by the same
power `𝒦 ᵉ` produces an object of `Coh(X, ℐ)` which is annihilated by `𝒦 ᵉ`, so that it is one of
the objects which hypothesis (1) speaks about. The two clauses are proved separately — that the
reduction is again a coherent adic system along `ℐ` is
`Stacks.Coherent.isCoherentAdicSystem_idealPowerQuotientSystem`, and the annihilation is
`Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot` applied termwise.

The second is the move that carries hypothesis (2) through that reduction. Dividing a morphism
of inverse systems by `𝒦 ᵉ` doubles the exponent of the annihilating power: from `𝒦 ᵗ` on the
levelwise kernels and cokernels of `α` one gets `𝒦 ²ᵗ` on those of the reduced morphism. This is
the source's first application of the remark of Tag 0888, taken over sheaves of modules from
`Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap`.

The third is the step at which hypothesis (1) is used. Carried to `X_e` by the pullback functor
of Tag 0887, the `𝒦 ᵉ`-reduction of `(F_n)` becomes an object of `Coh(X_e, ℐ_e)`, and hypothesis
(1) algebraizes it to a coherent `𝒪_{X_e}`-module `M`. Its direct image `G = i_* M` is a
coherent `𝒪_X`-module annihilated by `𝒦 ᵉ` whose completion along `ℐ` is the reduction we
started from: direct image commutes with completion by
`Stacks.Coherent.completionPushforwardIso`, and `i_* i^* F_n` is `F_n / 𝒦 ᵉ F_n` by Tag 0EL1,
which `Stacks.Coherent.idealPowerQuotientSystemPushforwardIso` assembles into an isomorphism of
systems.

The fourth is the assembly of the algebraizations of the third into a single object of
`Coh(X, 𝒦)`. The identification `G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ≅ G_e` that the assembly needs is read
off the completions: completion along `ℐ` turns the left-hand side into
`(F_n / 𝒦 ᵉ⁺² F_n) / 𝒦 ᵉ⁺¹ (…) ≅ F_n / 𝒦 ᵉ⁺¹ F_n`, which is the completion of the right-hand
side, and completion is fully faithful on the `𝒦 ᵉ⁺¹`-annihilated coherent modules by
`Stacks.Coherent.exists_unique_completion_preimage_of_power_annihilated`, a consequence of
hypothesis (1) proved in `CompletionFunctor.AnnihilatedFullyFaithful`.

The fifth is the fourth step again, in the form the rest of the source's argument needs: the
algebraizations `G_e` form a *tower* whose `ℐ`-completion is identified with the tower of
reductions naturally in `e`, the transitions being lifted through the same full faithfulness.
Only this natural form lets the comparison with `H ^∧_𝒦` be built.

The sixth is the source's passage from the comparison along `ℐ` to a comparison along `𝒦`: the
tower of algebraizations carries a map `γ : (G_e) ⟶ H ^∧_𝒦` whose levelwise kernels and
cokernels are annihilated by a power of `𝒦`, which is the hypothesis Tag 0889 asks for. The
comparison is the reduction of `α` lifted through the fullness of completion on the
`𝒦`-power-annihilated towers; the annihilation comes back from the completions.

The seventh is the case `ℐ ᵐ ≤ 𝒦` of the whole lemma. There hypothesis (2) is *already* the
hypothesis of Tag 0889 part (1): annihilation of the levelwise kernels and cokernels by `𝒦 ᵗ`
forces annihilation by `ℐ ᵐᵗ`, because `ℐ ᵐᵗ = (ℐ ᵐ) ᵗ ≤ 𝒦 ᵗ`. So the algebraization theorem
`Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian` applies to `α` directly and
produces the coherent module together with the isomorphism `(F_n) ≅ F ^∧` which the conclusion
asks for. Hypothesis (1) is not used in this case, and neither is any reduction modulo `𝒦`: the
whole force of the source's argument is in making hypothesis (2), which is stated for `𝒦`, usable
for `ℐ` when the two ideals are incomparable, and that is exactly what the containment removes.

Tag 088A itself closes the sixth step. Tag 0889 part (1) algebraizes `γ` to a coherent module
`M`, and the tower of algebraizations, read along the index of `(F_n)` instead of along the
exponent of `𝒦` (`Stacks.Coherent.liftedQuotientRowTowerIso`), turns that algebraization into an
identification of the `𝒦`-completions of the terms of `(F_n)` and of `M ^∧_ℐ`, compatible with
`α`. The uniqueness clause of Tag 0889, applied termwise, then identifies `(F_n)` with
`M ^∧_ℐ`; that is
`Stacks.Coherent.nonempty_iso_of_completion_iso_over_power_annihilated`.

## Main results

* `Stacks.Coherent.pow_le_pow_of_le_left` — powers of nested quasi-coherent ideal sheaves are
  nested.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_pow_le` — for `ℐ ᵐ ≤ 𝒦` the hypothesis
  of Tag 0888 (1) for `𝒦` implies the one for `ℐ`.
* `Stacks.Coherent.isCoherentAdicSystem_and_annihilated_idealPowerQuotientSystem` — the opening
  step of the proof of Tag 088A: the `𝒦 ᵉ`-reduction of a coherent adic system along `ℐ` is a
  coherent adic system along `ℐ` annihilated by `𝒦 ᵉ`.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_whiskerRight_idealPowerQuotientFunctor` —
  the second step: the `𝒦 ᵉ`-reduction of a morphism whose levelwise kernels and cokernels are
  annihilated by `𝒦 ᵗ` has them annihilated by `𝒦 ²ᵗ`.
* `Stacks.Coherent.idealPowerQuotientSystemPushforwardIso` — Tag 0EL1 for an inverse system:
  the `𝒦 ʳ`-reduction of a system of quasi-coherent modules is the direct image of its
  restriction to the closed subscheme cut out by `𝒦 ʳ`.
* `Stacks.Coherent.exists_coherent_annihilated_completion_iso_idealPowerQuotientSystem` — the
  third step: hypothesis (1) at the level `e` makes the `𝒦 ᵉ`-reduction of `(F_n)` the
  completion of a coherent `𝒪_X`-module annihilated by `𝒦 ᵉ`.
* `Stacks.Coherent.exists_coherentAdicSystem_completion_iso_idealPowerQuotientSystem` — the
  fourth step: the algebraizations `G_e` of the reductions assemble into an object of
  `Coh(X, 𝒦)`.
* `Stacks.Coherent.exists_lifted_quotient_tower` — the fourth step in its natural form: the
  `G_e` form a tower of coherent modules whose termwise `ℐ`-completion is isomorphic, naturally
  in `e`, to the tower of `𝒦 ᵉ⁺¹`-reductions of `(F_n)`.
* `Stacks.Coherent.exists_lifted_quotient_tower_comparison` — the fifth step: that tower carries
  a comparison `γ : (G_e) ⟶ H ^∧_𝒦` whose levelwise kernels and cokernels are annihilated by one
  positive power of `𝒦`.
* `Stacks.Coherent.essImage_completionFunctor_of_pow_le` — Tag 088A in the case `ℐ ᵐ ≤ 𝒦`,
  where hypothesis (1) is not needed.
* `Stacks.Coherent.essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower` —
  **[Stacks, Tag 088A]**.

## Implementation notes

The passage from `𝒦 ᵗ` to `𝒦 ²ᵗ` along a reduction is
carried in both of its forms: over modules by `Ideal.pow_le_annihilator_ker_mapQ_of_exact` and
`Ideal.pow_le_annihilator_coker_mapQ_of_exact`, over sheaves of modules by
`Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap`.

The order on quasi-coherent ideal sheaves and the formation of powers are both pointwise on the
ideals of sections, which is what makes `Stacks.Coherent.pow_le_pow_of_le_left` the pointwise
statement for ideals; the ideal-power multiple is then compared by
`Stacks.Algebraization.idealPowerMultiple_le_of_pow_le`.

`Stacks.Coherent.CoherentAdicSystems` is a full subcategory of `ℕᵒᵖ ⥤ X.Modules`, and the
algebraization theorem produces an isomorphism of the underlying inverse systems; it is promoted
to the subcategory by `CategoryTheory.ObjectProperty.isoMk`, which is what
`CategoryTheory.Functor.essImage` is asking for.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-! ### Powers of nested ideal sheaves -/

/-- For `ℐ ≤ 𝒦` the `t`-th powers satisfy `ℐ ᵗ ≤ 𝒦 ᵗ`.

Both the order on quasi-coherent ideal sheaves and the formation of powers are pointwise on the
ideals of sections over an affine open, so this is the corresponding statement for ideals of a
commutative ring. -/
public theorem pow_le_pow_of_le_left {I K : X.IdealSheafData} (h : I ≤ K) (t : ℕ) :
    I ^ t ≤ K ^ t :=
  Scheme.IdealSheafData.le_def.2 fun U =>
    pow_le_pow_left' (Scheme.IdealSheafData.le_def.1 h U) t

/-- If `ℐ ᵐ ≤ 𝒦` then `ℐ ᵐᵗ ≤ 𝒦 ᵗ`, by `pow_mul` and
`Stacks.Coherent.pow_le_pow_of_le_left`. -/
public theorem pow_mul_le_pow_of_pow_le {I K : X.IdealSheafData} {m : ℕ} (h : I ^ m ≤ K) (t : ℕ) :
    I ^ (m * t) ≤ K ^ t :=
  (pow_mul I m t).le.trans (pow_le_pow_of_le_left h t)

/-- If `ℐ ᵐ ≤ 𝒦` then a sheaf of modules annihilated by `𝒦 ᵗ` is annihilated by `ℐ ᵐᵗ`. -/
public theorem idealPowerMultiple_eq_bot_of_pow_le {I K : X.IdealSheafData} {m : ℕ}
    (h : I ^ m ≤ K) {t : ℕ} {M : X.Modules} (hM : idealPowerMultiple K t M = ⊥) :
    idealPowerMultiple I (m * t) M = ⊥ :=
  le_antisymm
    ((idealPowerMultiple_le_of_pow_le (pow_mul_le_pow_of_pow_le h t) M).trans hM.le) bot_le

/-- **The hypothesis of Tag 0888 (1) descends from `𝒦` to `ℐ` when `ℐ ᵐ ≤ 𝒦`.** If the levelwise
kernels and cokernels of `α` are annihilated by a power of `𝒦`, and some positive power of `ℐ` is
contained in `𝒦`, then they are annihilated by a power of `ℐ`.

This is what makes the case `ℐ ᵐ ≤ 𝒦` of Tag 088A immediate: hypothesis (2) of 088A, which is
stated for `𝒦`, becomes the hypothesis of Tag 0889 part (1), which is stated for `ℐ`. -/
public theorem isKernelCokernelAnnihilatedByPower_of_pow_le {I K : X.IdealSheafData} {m : ℕ}
    (hm : 0 < m) (h : I ^ m ≤ K)
    {F G : ℕᵒᵖ ⥤ X.Modules} {α : F ⟶ G}
    (hα : IsKernelCokernelAnnihilatedByPower K α) :
    IsKernelCokernelAnnihilatedByPower I α := by
  obtain ⟨t, ht, hkc⟩ := hα
  exact ⟨m * t, Nat.mul_pos hm ht, fun k => ⟨idealPowerMultiple_eq_bot_of_pow_le h (hkc k).1,
    idealPowerMultiple_eq_bot_of_pow_le h (hkc k).2⟩⟩

/-! ### The opening step: reducing the system modulo a power of the second ideal -/

/-- **Tag 088A, the opening step of the proof.** For a locally Noetherian `X`, quasi-coherent
ideal sheaves `ℐ, 𝒦`, an exponent `e` and a coherent adic system `(F_n)` along `ℐ`, the reduction
`n ↦ F_n / 𝒦 ᵉ F_n` is again a coherent adic system along `ℐ`, and every one of its terms is
annihilated by `𝒦 ᵉ`.

This is the sense in which the source's `(F_n / 𝒦 ᵉ F_n)` is "a system of `Coh(X, ℐ)`" lying in
the full subcategory of objects annihilated by `𝒦 ᵉ` — the subcategory which hypothesis (1) of
Tag 088A, read through the closed-immersion equivalence of Tag 087T, identifies with
`Coh(X_e, ℐ_e)`.

The first clause is `Stacks.Coherent.isCoherentAdicSystem_idealPowerQuotientSystem`, whose
substance is that the two orders of division agree. The second is
`Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot`, applied to each term; it
needs the term to be quasi-coherent, which is the coherence clause of the given system. -/
@[stacks 088A "proof step 1: the 𝒦ᵉ-reduction is in Coh(X, ℐ), annihilated by 𝒦ᵉ"]
public theorem isCoherentAdicSystem_and_annihilated_idealPowerQuotientSystem
    [IsLocallyNoetherian X] {I : X.IdealSheafData} (K : X.IdealSheafData) (e : ℕ)
    {F : ℕᵒᵖ ⥤ X.Modules} (hF : IsCoherentAdicSystem I F) :
    IsCoherentAdicSystem I (idealPowerQuotientSystem K e F) ∧
      ∀ n : ℕ, idealPowerMultiple K e ((idealPowerQuotientSystem K e F).obj (op n)) = ⊥ := by
  refine ⟨isCoherentAdicSystem_idealPowerQuotientSystem K e hF, fun n => ?_⟩
  have : (F.obj (op n)).IsQuasicoherent := hF.isQuasicoherent n
  exact idealPowerMultiple_idealPowerQuotient_eq_bot K e (F.obj (op n))

/-- **Tag 088A, the second step of the proof.** Reducing a morphism of inverse systems of
quasi-coherent modules modulo the fixed power `𝒦 ᵉ` doubles the exponent in hypothesis (2): if
`𝒦 ᵗ` annihilates every levelwise kernel and cokernel of `α`, then `𝒦 ²ᵗ` annihilates every
levelwise kernel and cokernel of
`n ↦ (F_n / 𝒦 ᵉ F_n ⟶ G_n / 𝒦 ᵉ G_n)`.

This is the source's first application of the remark of Tag 0888, which this library has over
sheaves of modules as
`Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap`; the source
applies it a second time further on and reaches `𝒦 ⁴ᵗ`.

Applied with `(G_n) = H ^∧` it is the statement that the comparison map of hypothesis (2) of
Tag 088A survives the reduction of the opening step with its kernel–cokernel condition intact,
which is what makes the reduced system an object to which Tag 0889 can be applied. -/
@[stacks 088A "proof step 2: the 𝒦ᵉ-reduction of a map with 𝒦ᵗ-annihilated kernel and cokernel \
has 𝒦²ᵗ-annihilated kernel and cokernel"]
public theorem isKernelCokernelAnnihilatedByPower_whiskerRight_idealPowerQuotientFunctor
    (K : X.IdealSheafData) (e : ℕ) {F G : ℕᵒᵖ ⥤ X.Modules}
    (hF : ∀ n : ℕ, (F.obj (op n)).IsQuasicoherent)
    (hG : ∀ n : ℕ, (G.obj (op n)).IsQuasicoherent)
    {α : F ⟶ G} (hα : IsKernelCokernelAnnihilatedByPower K α) :
    IsKernelCokernelAnnihilatedByPower K
      (Functor.whiskerRight α (idealPowerQuotientFunctor K e)) := by
  obtain ⟨t, ht, hkc⟩ := hα
  refine ⟨2 * t, by omega, fun k => ?_⟩
  have := hF k
  have := hG k
  exact idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap K K (α.app (op k))
    (hkc k).1 (hkc k).2 e

/-! ### The third step: hypothesis (1) algebraizes the reduction -/

/-- **[Stacks, Tag 0EL1] for an inverse system.** For a closed immersion `v` with ideal sheaf
`𝒦 ʳ` and an inverse system `(F_n)` of quasi-coherent modules, the termwise reduction
`n ↦ F_n / 𝒦 ʳ F_n` is the termwise direct image of the restriction of `(F_n)` along `v`.

Each component is `Stacks.Algebraization.idealQuotientPushforwardIso`; naturality is the
compatibility of that comparison with the adjunction unit, which is natural, after cancelling
the quotient projections. -/
public def idealPowerQuotientSystemPushforwardIso (K : X.IdealSheafData) (r : ℕ)
    {V : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v] (hv : v.ker = K ^ r)
    (F : ℕᵒᵖ ⥤ X.Modules) (hF : ∀ n : ℕᵒᵖ, (F.obj n).IsQuasicoherent) :
    idealPowerQuotientSystem K r F ≅
      F ⋙ Scheme.Modules.pullback v ⋙ Scheme.Modules.pushforward v := by
  refine NatIso.ofComponents (fun n =>
    haveI := hF n
    idealQuotientPushforwardIso K r (F.obj n) v hv) ?_
  intro m n f
  have := hF m
  have := hF n
  refine (cancel_epi (cokernel.π (C := X.Modules)
    (idealPowerMultiple K r (F.obj m)).ι)).1 ?_
  refine Eq.trans (b := F.map f ≫ (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app
    (F.obj n)) ?_ (Eq.symm ?_)
  · exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ idealQuotientPushforwardMap K r (F.obj n) v hv)
          (idealPowerQuotientMap_π K K r r le_rfl (F.map f))).trans
        ((Category.assoc (obj := X.Modules) _ _ _).trans
          (congrArg (fun z => F.map f ≫ z)
            (idealQuotientPushforwardMap_π K r (F.obj n) v hv))))
  · exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (Scheme.Modules.pushforward v).map
            ((Scheme.Modules.pullback v).map (F.map f)))
          (idealQuotientPushforwardMap_π K r (F.obj m) v hv)).trans
        ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.naturality (F.map f)).symm)

/-- **Tag 088A, the third step of the proof.** Let `X` be a Noetherian scheme, let `ℐ, 𝒦` be
quasi-coherent ideal sheaves, let `e` be an exponent and let `(F_n)` be an object of
`Coh(X, ℐ)`. If hypothesis (1) of Tag 088A holds at the level `e` — that is, the completion
functor of `X_e = V(𝒦 ᵉ⁺¹)` along `ℐ 𝒪_{X_e}` is an equivalence — then the `𝒦 ᵉ⁺¹`-reduction of
`(F_n)` is the completion of a coherent `𝒪_X`-module annihilated by `𝒦 ᵉ⁺¹`.

This is where hypothesis (1) enters. The reduction is carried to `X_e` by the pullback functor
of Tag 0887, where the hypothesis algebraizes it to a coherent module `M`; the algebraization on
`X` is `G = i_* M`, coherent by Tag 087T and annihilated by `𝒦 ᵉ⁺¹` because it is a direct image
along the inclusion of `V(𝒦 ᵉ⁺¹)`. The comparison of completions is
`Stacks.Coherent.completionPushforwardIso`, which identifies the completion of `i_* M` with the
direct image of the completion of `M`, followed by
`Stacks.Coherent.idealPowerQuotientSystemPushforwardIso`, which is Tag 0EL1 identifying
`i_* i^* F_n` with `F_n / 𝒦 ᵉ⁺¹ F_n`. -/
@[stacks 088A "proof step 3: hypothesis (1) algebraizes the 𝒦ᵉ-reduction"]
public theorem exists_coherent_annihilated_completion_iso_idealPowerQuotientSystem
    [IsNoetherian X] (I K : X.IdealSheafData) (e : ℕ) (Fsys : CoherentAdicSystems I)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence) :
    ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      idealPowerMultiple K (e + 1) G.obj = ⊥ ∧
      Nonempty (((completionFunctor X I).obj G).obj ≅
        idealPowerQuotientSystem K (e + 1) Fsys.obj) := by
  let i : (K ^ (e + 1)).subscheme ⟶ X := (K ^ (e + 1)).subschemeι
  have : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian i
  have : CompactSpace (K ^ (e + 1)).subscheme :=
    (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).compactSpace
  have : IsNoetherian (K ^ (e + 1)).subscheme := ⟨⟩
  have := h
  obtain ⟨M, ⟨cmp⟩⟩ := h.essSurj.mem_essImage ((coherentAdicPullback i I).obj Fsys)
  have hMc : M.obj.IsCoherent := M.property
  have hGc : ((Scheme.Modules.pushforward i).obj M.obj).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i M.obj
  have hGa : idealPowerMultiple K (e + 1) ((Scheme.Modules.pushforward i).obj M.obj) = ⊥ :=
    (annihilatedByKer_subschemeι_pow_iff K (e + 1) _).1
      ((Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal i _).mp
        ((Stacks.ClosedImmersion.pushforward_essImage_iff i _).mp
          ((Scheme.Modules.pushforward i).obj_mem_essImage M.obj)))
  refine ⟨⟨(Scheme.Modules.pushforward i).obj M.obj, hGc⟩, hGa, ⟨?_⟩⟩
  exact completionPushforwardIso i I M hGc ≪≫
    Functor.isoWhiskerRight ((ObjectProperty.ι (IsCoherentAdicSystem
      (I.comap i))).mapIso cmp) (Scheme.Modules.pushforward i) ≪≫
    (idealPowerQuotientSystemPushforwardIso K (e + 1) i
      (Scheme.IdealSheafData.ker_subschemeι _) Fsys.obj
      (fun n => Fsys.property.isQuasicoherent n.unop)).symm

/-! ### The tower of algebraizations -/

/-- **Tag 088A, the fourth step of the proof: the algebraizations assemble.** Let `X` be a
Noetherian scheme, let `ℐ, 𝒦` be quasi-coherent ideal sheaves and let `(F_n)` be an object of
`Coh(X, ℐ)`. If hypothesis (1) of Tag 088A holds at every level — the completion functor of
`X_e = V(𝒦 ᵉ⁺¹)` along `ℐ 𝒪_{X_e}` is an equivalence — then the coherent modules `G_e`
algebraizing the reductions `(F_n / 𝒦 ᵉ⁺¹ F_n)` form an object of `Coh(X, 𝒦)`.

The modules themselves and their defining property are the third step,
`Stacks.Coherent.exists_coherent_annihilated_completion_iso_idealPowerQuotientSystem`. What is
added here is the identification `G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ≅ G_e`, read off the completions by
`Stacks.Coherent.nonempty_idealPowerQuotient_iso_of_completion_iso`: completion along `ℐ`
carries the left-hand side to

`(F_n / 𝒦 ᵉ⁺² F_n) / 𝒦 ᵉ⁺¹ (…) ≅ F_n / 𝒦 ᵉ⁺¹ F_n`,

by `Stacks.Coherent.completionIdealPowerQuotientSystemIso` and
`Stacks.Coherent.idealPowerQuotientSystemCollapseIso`, which is the completion of the right-hand
side; and completion along `ℐ`, although not known to be full on all of `Coh(𝒪_X)`, is fully
faithful on the modules annihilated by `𝒦 ᵉ⁺¹`. The assembly of the identified modules into an
object of `Coh(X, 𝒦)` is `Stacks.Coherent.exists_coherentAdicSystem_of_succQuotientIso`.

The conclusion keeps the sequence `G` alongside the assembled system, because the rest of the
source's argument speaks about the terms: the comparison with `H ^∧` is built level by level. -/
@[stacks 088A "proof step 4: the algebraizations G_e assemble into an object of Coh(X, 𝒦)"]
public theorem exists_coherentAdicSystem_completion_iso_idealPowerQuotientSystem
    [IsNoetherian X] (I K : X.IdealSheafData) (Fsys : CoherentAdicSystems I)
    (h : ∀ e : ℕ,
      letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence) :
    ∃ Gsys : CoherentAdicSystems K,
      ∃ G : ℕ → AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        (∀ e : ℕ, Gsys.obj.obj (op e) = (G e).obj) ∧
        ∀ e : ℕ, idealPowerMultiple K (e + 1) (G e).obj = ⊥ ∧
          Nonempty (((completionFunctor X I).obj (G e)).obj ≅
            idealPowerQuotientSystem K (e + 1) Fsys.obj) := by
  choose G hann hc using fun e =>
    exists_coherent_annihilated_completion_iso_idealPowerQuotientSystem I K e Fsys (h e)
  have hqc : ∀ n : ℕᵒᵖ, (Fsys.obj.obj n).IsQuasicoherent :=
    fun n => Fsys.property.isQuasicoherent n.unop
  have he : ∀ e : ℕ,
      Nonempty (idealPowerQuotient K (e + 1) (G (e + 1)).obj ≅ (G e).obj) := by
    intro e
    refine nonempty_idealPowerQuotient_iso_of_completion_iso I K e (h e) (G (e + 1)) (G e)
      (hann e) ?_
    exact completionIdealPowerQuotientSystemIso I K (G (e + 1)) (e + 1) ≪≫
      Functor.isoWhiskerRight (hc (e + 1)).some (idealPowerQuotientFunctor K (e + 1)) ≪≫
      idealPowerQuotientSystemCollapseIso K (Nat.le_succ (e + 1)) Fsys.obj hqc ≪≫
      (hc e).some.symm
  obtain ⟨Gsys, hGsys⟩ := exists_coherentAdicSystem_of_succQuotientIso K
    (fun e => (G e).obj) (fun e => (G e).property) hann he
  exact ⟨Gsys, G, fun e => hGsys (op e), fun e => ⟨hann e, hc e⟩⟩

/-- **Tag 088A, the fourth step in the form the rest of the proof needs it.** Under hypothesis
(1) of Tag 088A at every level, the algebraizations `G_e` of the reductions
`(F_n / 𝒦 ᵉ⁺¹ F_n)` form a tower of coherent `𝒪_X`-modules, the term `e` annihilated by
`𝒦 ᵉ⁺¹`, whose termwise `ℐ`-completion is identified with the tower of reductions **naturally
in `e`**.

`Stacks.Coherent.exists_coherentAdicSystem_completion_iso_idealPowerQuotientSystem` assembles
the same modules into an object of `Coh(X, 𝒦)`, but its identification of completions is one
isomorphism for each `e` separately. What is added here is the naturality: the transition
`G_{e+1} ⟶ G_e` is obtained by lifting the transition of the tower of reductions through the
full faithfulness of completion on the `𝒦 ᵉ⁺²`-annihilated modules
(`Stacks.Coherent.exists_unique_completion_preimage_of_power_annihilated`), so the chosen
isomorphisms commute with the transitions by construction.

This is the datum that
`Stacks.Coherent.exists_tower_map_to_completion` consumes to produce the comparison
`(G_e) ⟶ H ^∧_𝒦` along `𝒦`. -/
@[stacks 088A "proof step 4, natural form: the algebraizations G_e form a tower whose \
ℐ-completion is the tower of 𝒦-power reductions of (F_n)"]
public theorem exists_lifted_quotient_tower [IsNoetherian X] (I K : X.IdealSheafData)
    (Fsys : CoherentAdicSystems I)
    (h : ∀ e : ℕ,
      letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence) :
    ∃ G : ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      (∀ e : ℕ, idealPowerMultiple K (e + 1) (G.obj (op e)).obj = ⊥) ∧
      Nonempty (G ⋙ completionFunctor X I ≅
        idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj Fsys) := by
  choose Gt hann hc using fun e =>
    exists_coherent_annihilated_completion_iso_idealPowerQuotientSystem I K e Fsys (h e)
  let cmp : ∀ e : ℕ, (completionFunctor X I).obj (Gt e) ≅
      (idealPowerQuotientAdicFunctor I K (e + 1)).obj Fsys := fun e =>
    ObjectProperty.isoMk (IsCoherentAdicSystem I) (hc e).some
  choose τ hτ using fun e =>
    (exists_unique_completion_preimage_of_power_annihilated I K (e + 1)
      (h (e + 1)) (Gt (e + 1)) (Gt e) (hann (e + 1))
      (idealPowerMultiple_eq_bot_of_le (hann e) (Nat.le_succ (e + 1)))
      ((cmp (e + 1)).hom ≫
        (idealPowerQuotientAdicDrop I K (Nat.le_succ (e + 1))).app Fsys ≫ (cmp e).inv)).exists
  have hnat : ∀ e : ℕ,
      (Functor.ofOpSequence τ ⋙ completionFunctor X I).map
            (homOfLE (Nat.le_add_right e 1)).op ≫ (cmp e).hom =
        (cmp (e + 1)).hom ≫ (idealPowerQuotientAdicTower I K ⋙
          (evaluation _ _).obj Fsys).map (homOfLE (Nat.le_add_right e 1)).op := by
    intro e
    refine Eq.trans (congrArg (fun z => z ≫ (cmp e).hom)
      ((congrArg (completionFunctor X I).map
        (Functor.ofOpSequence_map_homOfLE_succ τ e)).trans (hτ e))) ?_
    refine Eq.trans (Category.assoc (obj := CoherentAdicSystems I) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => (cmp (e + 1)).hom ≫ z)
      (Category.assoc (obj := CoherentAdicSystems I) _ _ _)) ?_
    refine Eq.trans (congrArg (fun z => (cmp (e + 1)).hom ≫
      (idealPowerQuotientAdicDrop I K (Nat.le_succ (e + 1))).app Fsys ≫ z)
        (cmp e).inv_hom_id) ?_
    refine Eq.trans (congrArg (fun z => (cmp (e + 1)).hom ≫ z) (Category.comp_id _)) ?_
    exact congrArg (fun φ : idealPowerQuotientAdicFunctor I K (e + 1 + 1) ⟶
        idealPowerQuotientAdicFunctor I K (e + 1) =>
      (cmp (e + 1)).hom ≫ φ.app Fsys) (idealPowerQuotientAdicTower_map_succ I K e).symm
  exact ⟨Functor.ofOpSequence τ, fun e => hann e,
    ⟨NatIso.ofComponents (fun e => cmp e.unop)
      (fun g => (NatTrans.ofOpSequence
        (F := Functor.ofOpSequence τ ⋙ completionFunctor X I)
        (G := idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj Fsys)
        (fun e => (cmp e).hom) hnat).naturality g)⟩⟩

/-- **Tag 088A, the fifth step: the comparison along `𝒦` exists and satisfies the hypothesis of
Tag 0889.** Let `X` be Noetherian, let `ℐ, 𝒦` be quasi-coherent ideal sheaves satisfying
hypothesis (1) of Tag 088A at every level, and let `α : (F_n) ⟶ H ^∧_ℐ` be a comparison whose
levelwise kernels and cokernels are annihilated by a power of `𝒦` — hypothesis (2). Then the
tower `(G_e)` of algebraizations of the reductions carries a morphism `γ : (G_e) ⟶ H ^∧_𝒦` whose
kernels and cokernels are annihilated by a single positive power of `𝒦`.

This is the whole of the source's passage from the comparison along `ℐ` to the comparison along
`𝒦`: the tower is `Stacks.Coherent.exists_lifted_quotient_tower`, the comparison is
`Stacks.Coherent.exists_tower_map_to_completion` — the reduction of `α` lifted through the
fullness of completion on `𝒦`-power-annihilated towers — and the annihilation is
`Stacks.Coherent.idealPowerMultiple_kernel_cokernel_tower_map_eq_bot`, the remark of Tag 0888
followed by the reflection of annihilation along completion.

What remains of the proof of Tag 088A after this is the final identification: Tag 0889 applied
to `γ` algebraizes it, and its uniqueness clause, threaded through the two towers, identifies
`(F_n)` with the completion of the resulting module. -/
@[stacks 088A "proof step 5: the comparison (G_e) ⟶ H^∧_𝒦 along 𝒦, with its levelwise kernels \
and cokernels annihilated by a power of 𝒦"]
public theorem exists_lifted_quotient_tower_comparison [IsNoetherian X]
    (I K : X.IdealSheafData) (Fsys : CoherentAdicSystems I)
    (h : ∀ e : ℕ,
      letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (α : Fsys ⟶ (completionFunctor X I).obj H)
    (hα : IsKernelCokernelAnnihilatedByPower K α.hom) :
    ∃ (G : ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (γ : G ⟶ completionTermTower K H),
      (∀ e : ℕ, idealPowerMultiple K (e + 1) (G.obj (op e)).obj = ⊥) ∧
      Nonempty (G ⋙ completionFunctor X I ≅
        idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj Fsys) ∧
      ∃ s : ℕ, 0 < s ∧ ∀ e : ℕ,
        idealPowerMultiple K s (kernel (C := X.Modules) (γ.app (op e)).hom) = ⊥ ∧
          idealPowerMultiple K s (cokernel (C := X.Modules) (γ.app (op e)).hom) = ⊥ := by
  obtain ⟨t, ht, hkc⟩ := hα
  obtain ⟨G, hG, ⟨c⟩⟩ := exists_lifted_quotient_tower I K Fsys h
  obtain ⟨b, hb⟩ := exists_tower_map_to_completion I K Fsys H α G h hG c
  exact ⟨G, b, hG, ⟨c⟩, 2 * t + 1, by omega, fun e =>
    idealPowerMultiple_kernel_cokernel_tower_map_eq_bot I K Fsys H α G h hG c b hb t hkc e⟩

/-! ### The case of nested ideals -/

/-- **Tag 088A in the case `ℐ ᵐ ≤ 𝒦`.** Let `X` be a Noetherian scheme, let `ℐ, 𝒦` be
quasi-coherent ideal sheaves on `X` with `ℐ ᵐ ≤ 𝒦` for some `m ≥ 1`, let `H` be a coherent
`𝒪_X`-module and let `(F_n)` be an object of `Coh(X, ℐ)` admitting a map `α : (F_n) ⟶ H ^∧`
whose levelwise kernels and cokernels are annihilated by a power of `𝒦`. Then `(F_n)` is in the
essential image of the completion functor of Tag 0880.

Hypothesis (1) of the source is not needed here, and no reduction modulo a power of `𝒦` occurs:
the containment turns hypothesis (2) into the hypothesis of Tag 0889 part (1) by
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_pow_le`, and
`Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian` then algebraizes `α`,
delivering a coherent module `F` and an isomorphism `(F_n) ≅ F ^∧`. The isomorphism is of the
underlying inverse systems and is promoted to the full subcategory `Coh(X, ℐ)` by
`CategoryTheory.ObjectProperty.isoMk`.

The source's own application has `ℐ` the pullback of an ideal of the base and `𝒦` the ideal of
the complement of the dense open on which Chow's lemma is an isomorphism; no power of `ℐ` is
contained in `𝒦` there, so this case does not cover it. -/
@[stacks 088A "the case ℐᵐ ≤ 𝒦, hypothesis (1) unused; incomparable case not claimed"]
public theorem essImage_completionFunctor_of_pow_le [IsNoetherian X] {I K : X.IdealSheafData}
    {m : ℕ} (hm : 0 < m) (hIK : I ^ m ≤ K)
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj H).obj)
    (hα : IsKernelCokernelAnnihilatedByPower K α) :
    (completionFunctor X I).essImage Fsys := by
  obtain ⟨F, a, β, -⟩ := exists_unique_algebraization_of_isNoetherian I H Fsys α
    (isKernelCokernelAnnihilatedByPower_of_pow_le hm hIK hα)
  exact ⟨F, ⟨ObjectProperty.isoMk (IsCoherentAdicSystem I) β.symm⟩⟩

/-! ### The theorem -/

/-- **[Stacks, Tag 088A].** Let `X` be a Noetherian scheme and let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent
ideal sheaves. Let `(F_n)` be an object of `Coh(X, ℐ)` and suppose

1. for every `e`, completion along `ℐ 𝒪_{X_e}` is an equivalence on `Coh(𝒪_{X_e})`, where
   `X_e = V(𝒦 ᵉ⁺¹)` is the closed subscheme cut out by the positive power `𝒦 ᵉ⁺¹`, and
2. there is a coherent `𝒪_X`-module `H` and a morphism `α : (F_n) ⟶ H ^∧_ℐ` whose levelwise
   kernels and cokernels are annihilated by a power of `𝒦`.

Then `(F_n)` is in the essential image of the completion functor of [Stacks, Tag 0880]: it is
the `ℐ`-completion of a coherent `𝒪_X`-module.

The proof is the source's, assembled from the steps carried above and in
`FormalGeometry.CoherentAdicSystem`. Dividing `(F_n)` by the powers of `𝒦` and algebraizing the
reductions with hypothesis (1) produces the tower `(G_e)` of
`Stacks.Coherent.exists_lifted_quotient_tower`, which is an object of `Coh(X, 𝒦)` by
`Stacks.Coherent.isCoherentAdicSystem_liftedQuotientTower`; the reduction of `α`, lifted through
the fullness of completion on the annihilated towers, is the comparison
`γ : (G_e) ⟶ H ^∧_𝒦` of `Stacks.Coherent.exists_tower_map_to_completion`, and its levelwise
kernels and cokernels are annihilated by one power of `𝒦`
(`Stacks.Coherent.idealPowerMultiple_kernel_cokernel_tower_map_eq_bot`). So [Stacks, Tag 0889]
part (1) algebraizes `γ` to a coherent module `M` with `(G_e) ≅ M ^∧_𝒦`.

What remains is to recognize `(F_n)` as `M ^∧_ℐ`. Reading the identification of the completed
tower `(G_e) ^∧_ℐ` with the tower of reductions of `(F_n)` along the *other* index
(`Stacks.Coherent.liftedQuotientRowTowerIso`) turns the algebraization of `γ` into an
identification of the `𝒦`-completions of the terms of `(F_n)` and of `M ^∧_ℐ`, compatible with
`α` and with `α ^∧` by `Stacks.Coherent.liftedQuotientRowIso_map_to_completion`; the uniqueness
clause of Tag 0889 applied termwise then identifies the two systems, which is
`Stacks.Coherent.nonempty_iso_of_completion_iso_over_power_annihilated`.

`Stacks.Coherent.essImage_completionFunctor_of_pow_le` is the special case `ℐ ᵐ ≤ 𝒦`, where
hypothesis (1) is not needed. -/
@[stacks 088A]
public theorem essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower [IsNoetherian X]
    (I K : X.IdealSheafData) (Fsys : CoherentAdicSystems I)
    (h : ∀ e : ℕ,
      letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (α : Fsys ⟶ (completionFunctor X I).obj H)
    (hα : IsKernelCokernelAnnihilatedByPower K α.hom) :
    (completionFunctor X I).essImage Fsys := by
  obtain ⟨t, ht, hkc⟩ := hα
  obtain ⟨G, hG, ⟨c⟩⟩ := exists_lifted_quotient_tower I K Fsys h
  let Gsys : CoherentAdicSystems K :=
    ⟨G ⋙ ObjectProperty.ι _, isCoherentAdicSystem_liftedQuotientTower I K Fsys h G hG c⟩
  obtain ⟨b, hb⟩ := exists_tower_map_to_completion I K Fsys H α G h hG c
  let γ : Gsys ⟶ (completionFunctor X K).obj H :=
    ObjectProperty.homMk (Functor.whiskerRight b (ObjectProperty.ι _))
  have hγ : IsKernelCokernelAnnihilatedByPower K γ.hom :=
    ⟨2 * t + 1, by omega, fun k =>
      idealPowerMultiple_kernel_cokernel_tower_map_eq_bot I K Fsys H α G h hG c b hb t hkc k⟩
  obtain ⟨M, a, β, ⟨hfac, hka, hca⟩, -⟩ :=
    exists_unique_algebraization_of_isNoetherian K H Gsys γ.hom hγ
  let βa : Gsys ≅ (completionFunctor X K).obj M := ObjectProperty.isoMk (IsCoherentAdicSystem K) β
  have hβ : γ = βa.hom ≫ (completionFunctor X K).map a :=
    ObjectProperty.hom_ext (IsCoherentAdicSystem K) hfac
  let d : (coherentAdicTerms I).obj Fsys ⋙ completionFunctor X K ≅
      (coherentAdicTerms I).obj ((completionFunctor X I).obj M) ⋙ completionFunctor X K :=
    (liftedQuotientRowTowerIso I K Fsys Gsys c).symm ≪≫
      Functor.isoWhiskerLeft (idealPowerQuotientAdicTower K I)
        ((evaluation (CoherentAdicSystems K) (CoherentAdicSystems K)).mapIso βa) ≪≫
      completionQuotientTowerIso K I M
  have hdapp : ∀ n : ℕ, (d.app (op n)).hom =
      (liftedQuotientRowIso I K Fsys Gsys c n).inv ≫
        (idealPowerQuotientAdicFunctor K I (n + 1)).map βa.hom ≫
          (completionQuotientTowerTermIso K I M n).hom := fun _ => rfl
  have hterms : ∀ n : ℕ,
      IsPowerAnnihilated K (kernel (C := X.Modules)
          (((coherentAdicTerms I).map ((completionFunctor X I).map a)).app (op n)).hom) ∧
        IsPowerAnnihilated K (cokernel (C := X.Modules)
          (((coherentAdicTerms I).map ((completionFunctor X I).map a)).app (op n)).hom) := by
    obtain ⟨s, hs⟩ := hka
    obtain ⟨r, hr⟩ := hca
    intro n
    have hbig := completion_map_term_annihilated I K a
      (idealPowerMultiple_eq_bot_of_le hs (show s ≤ s + r + 1 by omega))
      (idealPowerMultiple_eq_bot_of_le hr (show r ≤ s + r + 1 by omega)) n
    exact ⟨⟨2 * (s + r + 1), hbig.1⟩, ⟨2 * (s + r + 1), hbig.2⟩⟩
  have hd : ∀ n : ℕ,
      (completionFunctor X K).map (((coherentAdicTerms I).map α).app (op n)) =
        (d.app (op n)).hom ≫ (completionFunctor X K).map
          (((coherentAdicTerms I).map ((completionFunctor X I).map a)).app (op n)) := by
    intro n
    rw [hdapp n]
    refine (cancel_epi (liftedQuotientRowIso I K Fsys Gsys c n).hom).mp ?_
    rw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc,
      ← completionQuotientTowerTermIso_naturality K I a n, ← Category.assoc,
      ← Functor.map_comp, ← hβ]
    exact (liftedQuotientRowIso_map_to_completion I K Fsys Gsys H α γ c hb n).symm
  obtain ⟨ee⟩ := nonempty_iso_of_completion_iso_over_power_annihilated I K α
    ((completionFunctor X I).map a)
    (fun n => ⟨t, (hkc n).1⟩) (fun n => ⟨t, (hkc n).2⟩)
    (fun n => (hterms n).1) (fun n => (hterms n).2) d hd
  exact ⟨M, ⟨ee⟩⟩

end Stacks.Coherent

end
