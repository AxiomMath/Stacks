module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GeneralBaseAlgebraization
public import StacksCore.Tactic.StacksAttribute

/-!
# `lim δ` is a monomorphism: Stacks 02OC in degree zero, in the relative sheaf form

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent
sheaf of ideals, set `ℐ = f^{-1}𝒥 𝒪_X` and let `𝓕` be a coherent `𝒪_X`-module. The comparison
`δ : (f_*𝓕) ^∧ ⟶ f_*(𝓕 ^∧)` of
`Stacks.Coherent.directImageQuotientComparisonSystem` is **not** a monomorphism of inverse
systems: a monomorphism of inverse systems in `Y.Modules` is one levelwise, and the kernel of

`δ_m : (f_*𝓕) / 𝒥 ᵐ (f_*𝓕) ⟶ f_*(𝓕 / ℐ ᵐ 𝓕)`

is `f_*(ℐ ᵐ 𝓕) / 𝒥 ᵐ (f_*𝓕)`, which the uniform Artin–Rees bounds of Stacks 02OB squeeze between
powers of `𝒥` but do not kill. It becomes injective only after passing to the inverse limit, and
that statement is the theorem on formal functions, Stacks 02OC, in degree zero and in the
relative form `lim ((f_*𝓕) ^∧) ⟶ lim (f_*(𝓕 ^∧))` of sheaves on the base.

This file proves that statement, from the degree-zero Artin–Rees bound for the direct image as a
hypothesis, and so discharges the binder
`hmono : Mono (limMap (directImageQuotientComparisonSystem f J F))` of
`Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq`
(`CompletionProper/GeneralBaseAlgebraization.lean`), the uniqueness clause of the proof of
Stacks 088B at a general base.

## Main definitions

* `Stacks.Coherent.IsDirectImageAdicBounded` — **the degree-zero Artin–Rees bound for the direct
  image**: for every `n` there is an `m ≥ n` such that the kernel of
  `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` dies in `(f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)`. That kernel is `f_*(ℐ ᵐ⁺¹ 𝓕)`, so
  the condition reads `f_*(ℐ ᵐ⁺¹ 𝓕) ⊆ 𝒥 ⁿ⁺¹ (f_*𝓕)`, which is clause (1) of Stacks 02OB in
  degree zero — see the discussion below.

## Main results

* `Stacks.Coherent.mono_limMap_of_forall_kernel_comp_map_eq_zero` — **the passage to the limit.**
  In any abelian category, a morphism `δ` of diagrams whose levelwise kernels are killed by a
  transition map — for each index `n` there is an `m` and an arrow `g : m ⟶ n` with
  `ker δ_m ⟶ A_m ⟶ A_n` zero — has `lim δ` a monomorphism. Nothing is assumed about the shape of
  the diagrams, and no Mittag-Leffler hypothesis enters: the limit of a system of kernels whose
  transitions vanish is zero, and `lim` is left exact.
* `Stacks.Coherent.kernel_directImageQuotientComparisonApp_comp_map_eq_zero` — **the kernel of
  `δ_m`, bounded.** Granted the Artin–Rees bound at the pair `n ≤ m`, the composite
  `ker δ_m ⟶ (f_*𝓕) / 𝒥 ᵐ⁺¹ (f_*𝓕) ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)` is zero. This is the computation of
  `ker δ_m`: the projection `f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ᵐ⁺¹ (f_*𝓕)` is an epimorphism and carries the
  kernel of `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` onto `ker δ_m`, by
  `Stacks.Coherent.completionProjection_directImageQuotientComparisonApp`.
* `Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem` — **the deliverable:**
  `Mono (limMap (directImageQuotientComparisonSystem f J F))`, granted
  `Stacks.Coherent.IsDirectImageAdicBounded`.
* `Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq_of_adicBounded` — the
  uniqueness clause of the proof of Stacks 088B with its binder replaced by the Artin–Rees
  bound; this is the form the consumer wants.
* `Stacks.Coherent.pushforward_idealPowerMultiple_comp_completionProjection_eq_zero` — the bound
  read as the containment of subsheaves `f_*(ℐ ᵐ⁺¹ 𝓕) ⊆ 𝒥 ⁿ⁺¹ (f_*𝓕)` that the source writes,
  which fixes the meaning of the predicate.

## Why the hypothesis is the Artin–Rees bound and why it is not discharged here

The condition `Stacks.Coherent.IsDirectImageAdicBounded` is stated with `kernel.ι`, i.e. as

`Ker(f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)) ⊆ Ker(f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕))`,

and that is deliberate: it is the exact shape in which this library's Stacks 02OB delivers its
first clause. `Stacks.Cohomology.FormalFunctions.ker_cohomology_idealPowerQuotient_le`
(`FormalFunctions/IdealPowerQuotientCohomologyBoundProper.lean`) produces, for `A` Noetherian,
`g : Z ⟶ Spec A` proper and `ℱ` coherent, a single `c` with

`Ker(Hᵖ(Z, ℱ) → Hᵖ(Z, ℱ / 𝓘ⁿℱ)) ⊆ Iⁿ⁻ᶜ · Hᵖ(Z, ℱ)` for `n ≥ c`,

which in degree `p = 0` is precisely the inclusion above, read on global sections over an affine
base: `H⁰(Z, ℱ) = Γ(Y, f_*ℱ)` and `Iⁿ⁻ᶜ · Γ(Y, f_*ℱ)` is the sections of
`𝒥 ⁿ⁻ᶜ (f_*ℱ)` over an affine. Since the bound is `Iⁿ⁻ᶜ` rather than `Iⁿ`, the quantifier shape
of `Stacks.Coherent.IsDirectImageAdicBounded` is `∀ n, ∃ m ≥ n`, not a containment at a fixed
level — which is all the limit argument needs, and all that is true.

What is **not** available at this pin, and what keeps the bound a hypothesis, is the passage from
that statement about `A`-modules of global sections over an **affine** base to the containment of
subsheaves of `f_*𝓕` over a general Noetherian base `Y`. It needs the identification of
`Hᵖ(X, 𝓕)` in degree zero with `Γ(Y, f_*𝓕)` as the restriction of scalars along
`Stacks.Algebraization.baseRingHom`, the identification of `Iᵏ · Γ(Y, f_*𝓕)` with the sections of
`Stacks.Algebraization.idealPowerMultiple` over an affine — which is
`Stacks.Algebraization.idealPowerMultiple_obj_affineOpen`, available — and then a cover of `Y` by
finitely many affine opens over each of which the morphism `f` restricts to a proper morphism to
an affine, together with *one* exponent serving every member. The last of these is the real cost:
the Artin–Rees constant of `Stacks.Cohomology.FormalFunctions.ker_cohomology_idealPowerQuotient_le`
depends on the affine open, and the uniformity over a finite cover is not assembled in this
library. The same obstruction is recorded for the sheaf-level Artin–Rees of a monomorphism in the
implementation notes of `StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicArtinRees.lean`, where
it is resolved for a *fixed finite* cover and a conclusion about sections over `⊤`; here the
conclusion is a containment of subsheaves, so the cover cannot be fixed in advance.

Accordingly nothing below is weakened: the limit statement, which is the content of Stacks 02OC
in degree zero once 02OB is known, is a theorem, and the Artin–Rees bound it consumes is a named
predicate with a precise mathematical meaning rather than an opaque binder.

## References

* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

/-! ### The passage to the limit -/

/-- A map killed by `k` composes to zero with any `g` that kills the kernel of `k`. -/
private theorem comp_eq_zero_of_kernel_ι_comp_eq_zero {C : Type*} [Category C] [Abelian C]
    {P Q R T : C} {k : P ⟶ Q} {g : P ⟶ R} (h : kernel.ι k ≫ g = 0) {x : T ⟶ P}
    (hx : x ≫ k = 0) : x ≫ g = 0 := by
  rw [← kernel.lift_ι k x hx, Category.assoc, h, comp_zero]

section LimitPassage

variable {Jc : Type*} [Category Jc] {C : Type*} [Category C] [Abelian C]
  {A B : Jc ⥤ C} [HasLimit A] [HasLimit B]

/-- **A morphism of diagrams whose levelwise kernels are killed by a transition map becomes a
monomorphism after passing to the limit.** Let `δ : A ⟶ B` be a morphism of diagrams in an
abelian category and suppose that for every index `n` there are an index `m` and an arrow
`g : m ⟶ n` with the composite `ker δ_m ⟶ A_m ⟶ A_n` zero. Then `lim δ` is a monomorphism.

This is the one general fact behind Stacks 02OC in degree zero: the levelwise kernels of the
comparison `δ` of Stacks 088B do not vanish, but each of them dies in an earlier term of the
system, and the limit sees only what survives every transition.

The proof is `CategoryTheory.Preadditive.mono_iff_cancel_zero`: a map `u` into `lim A` killed by
`lim δ` has `u ≫ π_m` killed by `δ_m`, hence factoring through `ker δ_m`, hence `u ≫ π_n` zero
for the earlier index. No Mittag-Leffler condition and no exactness of `lim` beyond the universal
property is used. -/
public theorem mono_limMap_of_forall_kernel_comp_map_eq_zero (δ : A ⟶ B)
    (h : ∀ n : Jc, ∃ (m : Jc) (g : m ⟶ n), kernel.ι (δ.app m) ≫ A.map g = 0) :
    Mono (limMap δ) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T u hu
  refine limit.hom_ext fun n => ?_
  obtain ⟨m, g, hg⟩ := h n
  have hzero : (u ≫ limit.π A m) ≫ δ.app m = 0 := by
    rw [Category.assoc, ← limMap_π δ m, ← Category.assoc, hu, zero_comp]
  rw [← limit.w A g, ← Category.assoc, comp_eq_zero_of_kernel_ι_comp_eq_zero hg hzero, zero_comp]

end LimitPassage

/-! ### The Artin–Rees bound for the direct image, and the kernel of `δ_m` -/

section DirectImage

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The degree-zero Artin–Rees bound for the direct image.** For every `n` there is an `m ≥ n`
such that the kernel of `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` is killed by the projection
`f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)`.

The direct image of a coherent module along a proper morphism is left exact, so that kernel is
`f_*(ℐ ᵐ⁺¹ 𝓕)`, and the condition reads `f_*(ℐ ᵐ⁺¹ 𝓕) ⊆ 𝒥 ⁿ⁺¹ (f_*𝓕)`. Over an affine base it is
clause (1) of Stacks 02OB in degree zero,
`Stacks.Cohomology.FormalFunctions.ker_cohomology_idealPowerQuotient_le`, whose bound `Iⁿ⁻ᶜ` is
exactly what forces the `∀ n, ∃ m ≥ n` shape here rather than a containment level by level. See
the module docstring for what stands between that statement and this one. -/
public def IsDirectImageAdicBounded : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧
    kernel.ι (C := Y.Modules)
        ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) ≫
      completionProjection Y J (properPushforwardCoherent f F) n = 0

/-- **The kernel of `δ_m` dies at level `n`.** Granted the Artin–Rees bound at a pair `n ≤ m` —
the kernel of `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` is killed by the projection onto
`(f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)` — the composite

`ker δ_m ⟶ (f_*𝓕) / 𝒥 ᵐ⁺¹ (f_*𝓕) ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)`

is zero.

This is the computation of `ker δ_m` in the only form the limit argument needs. The projection
`q_m : f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ᵐ⁺¹ (f_*𝓕)` is an epimorphism
(`Stacks.Algebraization.epi_completionProjection`) and satisfies
`q_m ≫ δ_m = f_*(𝓕 ⟶ 𝓕 / ℐ ᵐ⁺¹ 𝓕)`
(`Stacks.Coherent.completionProjection_directImageQuotientComparisonApp`), so the preimage of
`ker δ_m` along `q_m` is the kernel of `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)`. The preimage is taken up to
refinements (`CategoryTheory.surjective_up_to_refinements_of_epi`), which is what replaces the
element chase of the source in an arbitrary abelian category. -/
public theorem kernel_directImageQuotientComparisonApp_comp_map_eq_zero {m n : ℕ} (hmn : n ≤ m)
    (har : kernel.ι (C := Y.Modules)
        ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) ≫
      completionProjection Y J (properPushforwardCoherent f F) n = 0) :
    kernel.ι (C := Y.Modules) (directImageQuotientComparisonApp f J F m) ≫
        ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj.map
          (homOfLE hmn).op = 0 := by
  have hepi := Stacks.Algebraization.epi_completionProjection Y J
    (properPushforwardCoherent f F) m
  obtain ⟨T, ρ, hρ, x, hx⟩ := surjective_up_to_refinements_of_epi (C := Y.Modules)
    (completionProjection Y J (properPushforwardCoherent f F) m)
    (kernel.ι (C := Y.Modules) (directImageQuotientComparisonApp f J F m))
  -- `x` lifts the kernel inclusion through the projection, so it is killed by `f_*(π_m)`
  have hx0 : x ≫ (Scheme.Modules.pushforward f).map
      (completionProjection X (J.comap f) F m) = 0 :=
    (congrArg (fun z => x ≫ z)
        (completionProjection_directImageQuotientComparisonApp f J F m).symm).trans
      ((Category.assoc (obj := Y.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ directImageQuotientComparisonApp f J F m) hx.symm).trans
          ((Category.assoc (obj := Y.Modules) _ _ _).trans
            ((congrArg (fun z => ρ ≫ z)
                (kernel.condition (C := Y.Modules)
                  (directImageQuotientComparisonApp f J F m))).trans
              (comp_zero (C := Y.Modules))))))
  -- hence, by the Artin--Rees bound, by the projection at level `n`
  have hxn : x ≫ completionProjection Y J (properPushforwardCoherent f F) n = 0 :=
    comp_eq_zero_of_kernel_ι_comp_eq_zero har hx0
  -- and `ρ` is an epimorphism
  refine (@cancel_epi _ _ _ _ _ ρ hρ _ _).mp ?_
  exact ((Category.assoc (obj := Y.Modules) _ _ _).symm.trans
    ((congrArg (fun z => z ≫ ((completionFunctor Y J).obj
          (properPushforwardCoherent f F)).obj.map (homOfLE hmn).op) hx).trans
      ((Category.assoc (obj := Y.Modules) _ _ _).trans
        ((congrArg (fun z => x ≫ z)
            (Stacks.Algebraization.completionProjection_map Y J
              (properPushforwardCoherent f F) (homOfLE hmn).op)).trans hxn)))).trans
    (comp_zero (C := Y.Modules)).symm

/-- **The Artin–Rees bound read as a containment of subsheaves of `f_*𝓕`.** Granted the bound at
a pair `m`, `n`, the composite

`f_*(ℐ ᵐ⁺¹ 𝓕) ⟶ f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)`

is zero — that is, `f_*(ℐ ᵐ⁺¹ 𝓕) ⊆ 𝒥 ⁿ⁺¹ (f_*𝓕)`, which is the form in which the source writes
the bound. Only left exactness of the direct image in the weak form
`f_*(ℐ ᵐ⁺¹ 𝓕 ⟶ 𝓕) ≫ f_*(𝓕 ⟶ 𝓕 / ℐ ᵐ⁺¹ 𝓕) = 0` is used, so the inclusion factors through the
kernel that the hypothesis kills.

This is stated to fix the meaning of `Stacks.Coherent.IsDirectImageAdicBounded`: the kernel the
predicate speaks of is `f_*(ℐ ᵐ⁺¹ 𝓕)`, and the predicate is the containment of that subsheaf of
`f_*𝓕` in a power of `𝒥` times `f_*𝓕`. -/
public theorem pushforward_idealPowerMultiple_comp_completionProjection_eq_zero {m n : ℕ}
    (har : kernel.ι (C := Y.Modules)
        ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) ≫
      completionProjection Y J (properPushforwardCoherent f F) n = 0) :
    (Scheme.Modules.pushforward f).map (idealPowerMultiple (J.comap f) (m + 1) F.obj).ι ≫
      completionProjection Y J (properPushforwardCoherent f F) n = 0 := by
  have : (Scheme.Modules.pushforward f).PreservesZeroMorphisms :=
    inferInstanceAs (Scheme.Modules.pushforward f).PreservesZeroMorphisms
  have hm0 : (Scheme.Modules.pushforward f).map
        ((idealPowerMultiple (J.comap f) (m + 1) F.obj).ι ≫
          cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) (m + 1) F.obj).ι) = 0 :=
    (congrArg (Scheme.Modules.pushforward f).map
      (cokernel.condition (C := X.Modules)
        (idealPowerMultiple (J.comap f) (m + 1) F.obj).ι)).trans (Functor.map_zero _ _ _)
  have hfac : (Scheme.Modules.pushforward f).map
        (idealPowerMultiple (J.comap f) (m + 1) F.obj).ι ≫
      (Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m) = 0 := by
    refine (congrArg (fun z => (Scheme.Modules.pushforward f).map
        (idealPowerMultiple (J.comap f) (m + 1) F.obj).ι ≫ z)
        ((Scheme.Modules.pushforward f).map_comp
          (cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) (m + 1) F.obj).ι)
          (eqToHom (completionFunctor_obj X (J.comap f) F m).symm))).trans ?_
    refine (Category.assoc (obj := Y.Modules) _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map
        (eqToHom (completionFunctor_obj X (J.comap f) F m).symm))
        (((Scheme.Modules.pushforward f).map_comp _ _).symm.trans hm0)).trans ?_
    exact zero_comp (C := Y.Modules)
  exact comp_eq_zero_of_kernel_ι_comp_eq_zero har hfac

/-- **Stacks 02OC in degree zero, in the relative sheaf form: `lim δ` is a monomorphism.** Let
`f : X ⟶ Y` be a proper morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf
of ideals, set `ℐ = f^{-1}𝒥 𝒪_X` and let `𝓕` be a coherent `𝒪_X`-module. Granted the degree-zero
Artin–Rees bound `Stacks.Coherent.IsDirectImageAdicBounded` for the direct image, the comparison
`δ : (f_*𝓕) ^∧ ⟶ f_*(𝓕 ^∧)` of
`Stacks.Coherent.directImageQuotientComparisonSystem` induces a **monomorphism**

`lim ((f_*𝓕) ^∧) ⟶ lim (f_*(𝓕 ^∧))`

of sheaves of `𝒪_Y`-modules.

This is the injectivity half of the theorem on formal functions in degree zero, in the relative
form of sheaves on the base. `δ` itself is not a monomorphism — a monomorphism of inverse systems
in `Y.Modules` is one levelwise, and `ker δ_m = f_*(ℐ ᵐ⁺¹ 𝓕) / 𝒥 ᵐ⁺¹ (f_*𝓕)` is not zero — so the
limit is where the statement lives.

The two inputs are
`Stacks.Coherent.kernel_directImageQuotientComparisonApp_comp_map_eq_zero`, which says each
levelwise kernel dies at an earlier level, and
`Stacks.Coherent.mono_limMap_of_forall_kernel_comp_map_eq_zero`, which says that this is enough
after the limit. -/
public theorem mono_limMap_directImageQuotientComparisonSystem
    (har : IsDirectImageAdicBounded f J F) :
    Mono (limMap (C := Y.Modules) (directImageQuotientComparisonSystem f J F)) := by
  refine mono_limMap_of_forall_kernel_comp_map_eq_zero _ fun n => ?_
  obtain ⟨m, hmn, h⟩ := har n.unop
  refine ⟨op m, (homOfLE hmn).op, ?_⟩
  rw [directImageQuotientComparisonSystem_app]
  exact kernel_directImageQuotientComparisonApp_comp_map_eq_zero f J F hmn h

/-- **The uniqueness clause of the proof of Stacks 088B, with its binder replaced by the
Artin–Rees bound.** Two morphisms out of a completion `𝒜 ^∧` with the same composite with
`Stacks.Coherent.directImageQuotientComparisonSystem` are equal, granted
`Stacks.Coherent.IsDirectImageAdicBounded`.

This is `Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq` with its hypothesis
`hmono` discharged by `Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem`. Together
with `Stacks.Coherent.isDirectImageCharacterized_iff_comp_directImageQuotientComparisonSystem` it
is the source's assertion that the characterized `α` is unique. -/
public theorem eq_of_comp_directImageQuotientComparisonSystem_eq_of_adicBounded
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (har : IsDirectImageAdicBounded f J F)
    {u v : ((completionFunctor Y J).obj 𝒜).obj ⟶
      ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj}
    (h : u ≫ directImageQuotientComparisonSystem f J F =
      v ≫ directImageQuotientComparisonSystem f J F) : u = v :=
  eq_of_comp_directImageQuotientComparisonSystem_eq f J F 𝒜
    (mono_limMap_directImageQuotientComparisonSystem f J F har) h

end DirectImage

end Stacks.Coherent

end
