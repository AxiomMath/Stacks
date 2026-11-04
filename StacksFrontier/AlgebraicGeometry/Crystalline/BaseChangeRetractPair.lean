module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeCompositeIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeHom

/-!
# `F ∘ G` is the identity functor, on the pairs themselves

The proof of [Stacks, Lemma 60.17.5, Tag 07L5] introduces the base change functors

`F : (M, ∇) ↦ (M ⊗^∧_{D, a} D', ∇')`   and   `G : (M', ∇') ↦ (M' ⊗^∧_{D', b} D, ∇)`

attached to the two divided power maps `a : D → D'`, `b : D' → D` of its first assertion, and
then says: "Since `a ∘ b = id_{D'}` we see that `F ∘ G` is the identity functor."

`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract` is that sentence read on
the completed de Rham complexes.  This module proves it on the categories of **pairs** of the
second assertion of [Stacks, Tag 07L5]: for a pair `(M', ∇')` over `D'` the round trip
`F (G (M', ∇'))` is isomorphic to `(M', ∇')` by a `D'`-linear **horizontal** bijection, namely
the composite

`(M' ⊗̂_{D', b} D) ⊗̂_{D, a} D' --ρ--> M' ⊗̂_{D', id} D' --collapse--> M'`

of `Crystalline.CompletedConnection.baseChangeComposite`, along `a ∘ b = id_{D'}`, and of
`Crystalline.CompletedConnection.baseChangeCollapse`, the inverse of the inclusion `m ↦ 1 ⊗ m`
for a `p`-adically complete `M'` (item [Stacks, Tag 07JB] of the pair).

## Main definitions

* `Crystalline.CompletedConnection.baseChangeCollapseEquiv` — the collapse of the base change
  along the identity, as a linear isomorphism.
* `Crystalline.CompletedConnection.retractComparison` — **the comparison
  `F (G M') → M'`**, the collapse of the composite.
* `Crystalline.CompletedConnection.retractComparisonEquiv` — it as a `D'`-linear isomorphism.

## Main results

* `Crystalline.CompletedConnection.baseChangeCollapse_bijective` — the collapse of the base
  change along the identity is bijective.
* `Crystalline.CompletedConnection.baseChange_baseChangeCollapse` — **horizontality of the
  collapse**.
* `Crystalline.CompletedConnection.retractComparison_inclusion` — the comparison undoes the two
  inclusions `m ↦ 1 ⊗ (1 ⊗ m)`.
* `Crystalline.CompletedConnection.baseChangeModuleMap_injective_of_retract` — **the base change
  along `b` is faithful**, which is faithfulness of the functor `G` on the underlying maps of its
  morphisms.
* `Crystalline.CompletedConnection.baseChange_retractComparison` — **horizontality of the
  comparison `F (G M') → M'`**.
* `Crystalline.CompletedConnection.exists_horizontalEquiv_of_retract` — **`F ∘ G` is the identity
  functor, on the pairs**: for `a ∘ b = id_{D'}` and comparisons of forms with `ψ' ∘ ψ = id`,
  there is a `D'`-linear horizontal bijection from the round trip `F (G (M', ∇'))` to
  `(M', ∇')`.

## What is and is not proved

**No `@[stacks 07L5]` attribute is placed in this module.**  That lemma has two assertions.  The
first, the retract between the rings, is `Crystalline.exists_completedEnvelopeRetract`.  The
second is an equivalence of categories of pairs, and what is proved here is the direction
`F ∘ G ≅ 𝟭` of it.  The whole lemma is `Crystalline.exists_presentation_retract_pairEquivalence`,
which carries the tag.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u v v' w

namespace Crystalline

namespace CompletedConnection

/-! ### The collapse of the base change along the identity -/

section Collapse

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type w) [AddCommGroup M] [Module D M]
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega] {d : D → Omega}
  (nabla : CompletedConnection p D Omega d M)

/-- **The collapse of the base change along the identity is bijective**, its inverse being the
inclusion `m ↦ 1 ⊗ m`. -/
public theorem baseChangeCollapse_bijective (hM : IsPAdicallyComplete p D M) :
    Function.Bijective (baseChangeCollapse p D M hM) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨baseChangeInclusion p D D M, inclusion_baseChangeCollapse p D M hM,
      baseChangeCollapse_inclusion p D M hM⟩

/-- The collapse of the base change along the identity, as a `D`-linear isomorphism. -/
public def baseChangeCollapseEquiv (hM : IsPAdicallyComplete p D M) :
    baseChangeCarrier p D D M ≃ₗ[D] M :=
  LinearEquiv.ofBijective (baseChangeCollapse p D M hM) (baseChangeCollapse_bijective p D M hM)

/-- `Crystalline.CompletedConnection.baseChangeCollapseEquiv` applies as the collapse. -/
@[simp] public theorem baseChangeCollapseEquiv_apply (hM : IsPAdicallyComplete p D M)
    (x : baseChangeCarrier p D D M) :
    baseChangeCollapseEquiv p D M hM x = baseChangeCollapse p D M hM x :=
  rfl

/-- **Horizontality of the collapse.**  The base change of `(M, ∇)` along the identity of `D`,
with the identity comparison of forms, is carried to `(M, ∇)` by the collapse, which is
horizontal. -/
public theorem baseChange_baseChangeCollapse (hM : IsPAdicallyComplete p D M)
    (hadd : ∀ x y : D, d (x + y) = d x + d y)
    (hleib : ∀ x y : D, d (x * y) = x • d y + y • d x) (x : baseChangeCarrier p D D M) :
    nabla (baseChangeCollapse p D M hM x) =
      valuesMap p D Omega (baseChangeCarrier p D D M) M (baseChangeCollapse p D M hM)
        (baseChange p D D M Omega Omega d LinearMap.id nabla hadd hleib (fun _ ↦ rfl) x) := by
  have hincl := baseChange_inclusion p D D M Omega Omega d LinearMap.id nabla hadd hleib
    (fun _ ↦ rfl) (baseChangeCollapse p D M hM x)
  rw [inclusion_baseChangeCollapse p D M hM x] at hincl
  rw [hincl]
  exact (baseChangeValuesCollapse_baseChangeValues p D M Omega hM
    (nabla (baseChangeCollapse p D M hM x))).symm

end Collapse

/-! ### The comparison `F (G M') → M'` -/

section Retract

variable (p : ℕ) (D : Type u) [CommRing D] (E : Type u) [CommRing E] [Algebra D E]
  [Algebra E D] [IsScalarTower D E D] (M : Type w) [AddCommGroup M] [Module D M]
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  (Omega' : Type v') [AddCommGroup Omega'] [Module E Omega']
  {d : D → Omega} (d' : E → Omega') (psi : Omega →ₛₗ[algebraMap D E] Omega')
  (psi' : Omega' →ₛₗ[algebraMap E D] Omega)
  (nabla : CompletedConnection p D Omega d M)

/-- **The comparison `F (G M') → M'`** of the round trip of base changes along a retract
`a ∘ b = id` with the module itself: the comparison
`Crystalline.CompletedConnection.baseChangeComposite` of the twice base-changed module with the
once base-changed one, followed by the collapse of the base change along the identity. -/
public def retractComparison (hM : IsPAdicallyComplete p D M) :
    baseChangeCarrier p E D (baseChangeCarrier p D E M) →ₗ[D] M :=
  baseChangeCollapse p D M hM ∘ₗ baseChangeComposite p D E D M

/-- The comparison `F (G M') → M'` is bijective, both of its factors being so. -/
public theorem retractComparison_bijective (hM : IsPAdicallyComplete p D M) :
    Function.Bijective (retractComparison p D E M hM) :=
  (baseChangeCollapse_bijective p D M hM).comp (baseChangeComposite_bijective p D E D M)

/-- **The comparison `F (G M') → M'` as a `D`-linear isomorphism.** -/
public def retractComparisonEquiv (hM : IsPAdicallyComplete p D M) :
    baseChangeCarrier p E D (baseChangeCarrier p D E M) ≃ₗ[D] M :=
  LinearEquiv.ofBijective (retractComparison p D E M hM)
    (retractComparison_bijective p D E M hM)

/-- `Crystalline.CompletedConnection.retractComparisonEquiv` applies as the comparison. -/
@[simp] public theorem retractComparisonEquiv_apply (hM : IsPAdicallyComplete p D M)
    (x : baseChangeCarrier p E D (baseChangeCarrier p D E M)) :
    retractComparisonEquiv p D E M hM x = retractComparison p D E M hM x :=
  rfl

/-- **The comparison undoes the two inclusions**: the composite
`m ↦ 1 ⊗ (1 ⊗ m)` of the canonical maps of the two base changes is a section of the comparison
`F (G M') → M'`. -/
@[simp] public theorem retractComparison_inclusion (hM : IsPAdicallyComplete p D M) (m : M) :
    retractComparison p D E M hM
        (baseChangeInclusion p E D (baseChangeCarrier p D E M)
          (baseChangeInclusion p D E M m)) = m := by
  rw [retractComparison, LinearMap.comp_apply, baseChangeComposite_inclusion,
    baseChangeCollapse_inclusion]

/-- **The base change along `b` is faithful on `D'`-linear maps**, which is faithfulness of the
functor `G` of the proof of [Stacks, Lemma 60.17.5, Tag 07L5] on the underlying maps of its
morphisms, for a `p`-adically complete target. -/
public theorem baseChangeModuleMap_injective_of_retract (N : Type w) [AddCommGroup N]
    [Module D N] (hN : IsPAdicallyComplete p D N) {f g : M →ₗ[D] N}
    (h : baseChangeModuleMap p D E M N f = baseChangeModuleMap p D E M N g) : f = g := by
  refine LinearMap.ext fun m ↦ ?_
  have key (k : M →ₗ[D] N) : k m =
      retractComparison p D E N hN
        (baseChangeModuleMap p E D (baseChangeCarrier p D E M) (baseChangeCarrier p D E N)
          (baseChangeModuleMap p D E M N k)
          (baseChangeInclusion p E D (baseChangeCarrier p D E M)
            (baseChangeInclusion p D E M m))) := by
    rw [baseChangeModuleMap_inclusion, baseChangeModuleMap_inclusion,
      retractComparison_inclusion]
  rw [key f, key g, h]

/-- **Horizontality of the comparison `F (G M') → M'`.** For comparisons of forms with
`ψ' ∘ ψ = id`, the comparison carries the twice base-changed connection to `∇`. -/
public theorem baseChange_retractComparison (hM : IsPAdicallyComplete p D M)
    (hadd : ∀ x y : D, d (x + y) = d x + d y)
    (hleib : ∀ x y : D, d (x * y) = x • d y + y • d x)
    (hadd' : ∀ x y : E, d' (x + y) = d' x + d' y)
    (hleib' : ∀ x y : E, d' (x * y) = x • d' y + y • d' x)
    (hpsi : ∀ x : D, psi (d x) = d' (algebraMap D E x))
    (hpsi' : ∀ x : E, psi' (d' x) = d (algebraMap E D x))
    (hretract : ∀ omega : Omega, psi' (psi omega) = omega)
    (x : baseChangeCarrier p E D (baseChangeCarrier p D E M)) :
    nabla (retractComparison p D E M hM x) =
      valuesMap p D Omega (baseChangeCarrier p E D (baseChangeCarrier p D E M)) M
        (retractComparison p D E M hM)
        (baseChange p E D (baseChangeCarrier p D E M) Omega' Omega d psi'
          (baseChange p D E M Omega Omega' d' psi nabla hadd' hleib' hpsi) hadd hleib hpsi'
          x) := by
  have hcomp := baseChange_baseChangeComposite p D E D M Omega Omega' Omega d' d psi psi'
    LinearMap.id nabla hadd' hleib' hpsi hadd hleib hpsi' (fun omega ↦ (hretract omega).symm)
    (fun _ ↦ rfl) x
  rw [retractComparison, LinearMap.comp_apply,
    baseChange_baseChangeCollapse p D M Omega nabla hM hadd hleib
      (baseChangeComposite p D E D M x),
    hcomp]
  exact (valuesMap_comp p D Omega
    (baseChangeCarrier p E D (baseChangeCarrier p D E M)) (baseChangeCarrier p D D M) M
    (baseChangeComposite p D E D M) (baseChangeCollapse p D M hM) _).symm

/-- **`F ∘ G` is the identity functor, read on the pairs themselves.**

For divided power maps `a : D → D'` and `b : D' → D` with `a ∘ b = id_{D'}` — here the
`IsScalarTower` instance, with `D` the source's `D'` and `E` the source's `D` — and comparisons
of forms `ψ` along `b` and `ψ'` along `a` with `ψ' ∘ ψ = id`, the round trip `F (G (M', ∇'))` of
base changes of a pair `(M', ∇')` over `D'` is isomorphic to `(M', ∇')`: there is a `D'`-linear
bijection carrying the twice base-changed connection to `∇'`.

This is the sentence "Since `a ∘ b = id_{D'}` we see that `F ∘ G` is the identity functor" of the
proof of [Stacks, Lemma 60.17.5, Tag 07L5], on pairs. -/
public theorem exists_horizontalEquiv_of_retract (hM : IsPAdicallyComplete p D M)
    (hadd : ∀ x y : D, d (x + y) = d x + d y)
    (hleib : ∀ x y : D, d (x * y) = x • d y + y • d x)
    (hadd' : ∀ x y : E, d' (x + y) = d' x + d' y)
    (hleib' : ∀ x y : E, d' (x * y) = x • d' y + y • d' x)
    (hpsi : ∀ x : D, psi (d x) = d' (algebraMap D E x))
    (hpsi' : ∀ x : E, psi' (d' x) = d (algebraMap E D x))
    (hretract : ∀ omega : Omega, psi' (psi omega) = omega) :
    ∃ e : baseChangeCarrier p E D (baseChangeCarrier p D E M) ≃ₗ[D] M,
      ∀ x : baseChangeCarrier p E D (baseChangeCarrier p D E M),
        nabla (e x) =
          valuesMap p D Omega (baseChangeCarrier p E D (baseChangeCarrier p D E M)) M
            e.toLinearMap
            (baseChange p E D (baseChangeCarrier p D E M) Omega' Omega d psi'
              (baseChange p D E M Omega Omega' d' psi nabla hadd' hleib' hpsi) hadd hleib
              hpsi' x) :=
  ⟨retractComparisonEquiv p D E M hM, baseChange_retractComparison p D E M Omega Omega' d' psi
    psi' nabla hM hadd hleib hadd' hleib' hpsi hpsi' hretract⟩

end Retract

end CompletedConnection

end Crystalline

end
