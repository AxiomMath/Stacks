module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientCohomologyBoundProper
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageLimitComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictGlue
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree-zero Artin–Rees bound for the direct image: the two steps that are available

`CompletionProper/DirectImageLimitComparison.lean` proves Stacks 02OC in degree zero and in the
relative sheaf form from one hypothesis, `Stacks.Coherent.IsDirectImageAdicBounded`: for every
`n` there is an `m ≥ n` with

`Ker(f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)) ⊆ Ker(f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕))`,

equivalently the containment of subsheaves `f_*(ℐ ᵐ⁺¹ 𝓕) ⊆ 𝒥 ⁿ⁺¹ (f_*𝓕)`. That is clause (1) of
Stacks 02OB in degree zero at the relative level. Its module docstring records what stands
between that hypothesis and the library's Stacks 02OB,
`Stacks.Cohomology.FormalFunctions.ker_cohomology_idealPowerQuotient_le`, which bounds the kernel
of `Hᵖ(X, ℱ) → Hᵖ(X, ℱ / 𝓘ⁿℱ)` by `Iⁿ⁻ᶜ · Hᵖ(X, ℱ)` for an **affine** base: two things, and
this file supplies both of them.

**The degree-zero bridge.** Nothing identified `H⁰` with global sections, so the bound of Stacks
02OB was unusable in degree zero. `Stacks.Cohomology.FormalFunctions.cohomologyOverBase` is the
`p`-th right derived functor of `Stacks.Cohomology.AffineBase.moduleGlobalSections` with scalars
restricted along `Stacks.Cohomology.FormalFunctions.baseRingHom`, and that functor is left exact,
so `CategoryTheory.Functor.rightDerivedZeroIsoSelf` identifies its degree-zero derived functor with
itself. `Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le` is clause (1)
of Stacks 02OB transported across that identification: the kernel of `Γ(X, ℱ) → Γ(X, ℱ / 𝓘ⁿℱ)` is
contained in `Iⁿ⁻ᶜ · Γ(X, ℱ)`, as `A`-submodules of `Γ(X, ℱ)`.

**One exponent for a cover of the base.** The conclusion wanted is a containment of *subsheaves* of
`f_*𝓕` on a general Noetherian base `Y`, while the Artin–Rees constant of Stacks 02OB depends on
the affine open of `Y` over which the morphism is read.
`Stacks.Coherent.IsDirectImageAdicBoundedOn` is the bound localized at an open of the base — one
constant `c`, valid for every pair `n + c ≤ m`, for the restriction of the comparison composite to
that open — and `Stacks.Coherent.isDirectImageAdicBounded_of_affineOpens` is the passage from it,
over every affine open, to `Stacks.Coherent.IsDirectImageAdicBounded`. The affine opens of a scheme
form a basis of its topology, so quasi-compactness of `Y` cuts them down to a finite subfamily
covering `Y` (`TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact`), the maximum of the
finitely many constants is one constant serving every member (`Finite.exists_le`), and equality of
morphisms of sheaves of modules is local
(`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover`). This is the idiom of
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_affineOpens`
(`CompletionProper/AnnihilationLocality.lean`), which needs `[CompactSpace Y]` and not
`[IsNoetherian Y]`, applied to the predicate at hand.

**The localized bound is a statement about sections over affine opens.** `𝒥 ⁿ⁺¹ (f_*𝓕)` is cut
out by the submodules `𝒥(W) ⁿ⁺¹ Γ(W, f_*𝓕)` over the affine opens `W` and membership in a
subsheaf is local on them, so
`Stacks.Coherent.isDirectImageAdicBoundedOn_of_forall_affineOpens` reduces the localized bound at
`V` to clause (1) of Stacks 02OB written out on the sections over each affine open `W ≤ V`: a
section of `f_*𝓕` over `W` killed by `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` lies in `𝒥(W) ⁿ⁺¹ Γ(W, f_*𝓕)`.
This is where the sheaf-theoretic plumbing on the base is discharged — the projection onto the
quotient is a cokernel in `Y.Modules`, so its sections over a general open are not a quotient of
the sections, while over an affine open they are — and after it the only thing still missing is
one constant for all the affine opens contained in `V` rather than one per affine open.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.globalSectionsOverBase` — `Γ(X, ℱ)` as a module over the
  base ring `A` of `f : X ⟶ Spec A`, the action being restriction of scalars along
  `Stacks.Cohomology.FormalFunctions.baseRingHom`. This is `cohomologyOverBase` in degree zero
  with the derived functor replaced by the functor.
* `Stacks.Coherent.IsDirectImageAdicBoundedOn` — the degree-zero Artin–Rees bound for the direct
  image **localized at an open `V` of the base**: one `c` such that for every `n + c ≤ m` the
  restriction to `V` of `ker(f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)) ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)` vanishes.

## Main results

* `Stacks.Cohomology.FormalFunctions.cohomologyOverBaseZeroIso` and
  `cohomologyOverBaseZeroIso_naturality` — **the degree-zero bridge**: `H⁰(X, ℱ)` as an
  `A`-module is `Γ(X, ℱ)` as an `A`-module, naturally in `ℱ`.
* `Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le` — **clause (1) of
  Stacks 02OB in degree zero, on global sections.**
* `Stacks.Coherent.isDirectImageAdicBounded_of_affineOpens` — **one exponent for a cover of the
  base**: the localized bound over every affine open of `Y` gives
  `Stacks.Coherent.IsDirectImageAdicBounded`.
* `Stacks.Coherent.isDirectImageAdicBoundedOn_of_forall_affineOpens` — **the localized bound from
  the sections over affine opens**: the containment of clause (1) of Stacks 02OB on the sections
  over every affine open contained in `V`, with one constant, gives
  `Stacks.Coherent.IsDirectImageAdicBoundedOn f J F V`.
* `Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem_of_affineOpens` and
  `Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq_of_affineOpens` — Stacks
  02OC in degree zero in the relative sheaf form, and the uniqueness clause of the proof of
  Stacks 088B, with the hypothesis in the localized form.

## What is still a hypothesis, and why

One thing is left as a binder, and after the three results above it is exactly one thing: the
hypothesis of `Stacks.Coherent.isDirectImageAdicBoundedOn_of_forall_affineOpens`, namely clause
(1) of Stacks 02OB on the sections over the affine opens contained in `V`, **with a single
constant for all of them**.

Over an affine open `W` of `Y` that constant is available. The morphism restricts to a proper
morphism `f ∣_ W : f⁻¹W ⟶ W` to an affine scheme
(`AlgebraicGeometry.IsProper.instMorphismRestrict` and `AlgebraicGeometry.IsAffineOpen.isoSpec`),
the restricted ideal sheaf is `(J.comap W.ι).comap (f ∣_ W) = (J.comap f).comap (f⁻¹W).ι`
(`Stacks.Coherent.comap_comap_morphismRestrict`, `CompletionProper/DirectImageRestrictOpen.lean`),
the restricted comparison is the comparison of the restriction
(`Stacks.Coherent.directImageQuotientComparison_restrict`, same file), and the sections of
`f_*𝓕` over `W` are the sections of `𝓕` over `f⁻¹W`
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`, by `rfl`). Through those,
`ker_globalSections_idealPowerQuotient_le` gives the containment on the sections over `W`, with
the constant `c` that Stacks 02OB produces for `f ∣_ W`.

That constant depends on `W`, and an affine open contained in `W` is not controlled by it. What
makes one constant serve all of them is that `Γ(W, 𝒪_Y) ⟶ Γ(W', 𝒪_Y)` is flat for `W' ≤ W` an
inclusion of affine opens, so that the kernel of a map of quasi-coherent modules and the
submodule `𝒥(W) ⁿ⁺¹ Γ(W, f_*𝓕)` both base change; the containment over `W` then gives the
containment over every affine `W' ≤ W` with the same constant. That flat base change is the step
the implementation notes of `StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicArtinRees.lean`
record as absent, and it is the reason that file fixes a finite affine cover in advance and
concludes only about the sections over `⊤`. It is the only thing between this file and
`Stacks.Coherent.IsDirectImageAdicBounded`.

## References

* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization

/-! ### The degree-zero bridge: `H⁰` is global sections -/

section DegreeZero

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- `Γ(X, ℱ)` as a module over the base ring `A` of `f : X ⟶ Spec A`, the action being
restriction of scalars along `Stacks.Cohomology.FormalFunctions.baseRingHom`.

This is `Stacks.Cohomology.FormalFunctions.cohomologyOverBase` in degree zero with the derived
functor of `Stacks.Cohomology.AffineBase.moduleGlobalSections` replaced by that functor itself;
`Stacks.Cohomology.FormalFunctions.cohomologyOverBaseZeroIso` identifies the two. -/
public abbrev globalSectionsOverBase (F : X.Modules) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (baseRingHom A f)).obj
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).obj F)

/-- `Γ(X, φ)` as an `A`-linear map. -/
public abbrev globalSectionsOverBaseMap {F G : X.Modules} (φ : F ⟶ G) :
    globalSectionsOverBase A f F ⟶ globalSectionsOverBase A f G :=
  (ModuleCat.restrictScalars (baseRingHom A f)).map
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).map φ)

/-- **The degree-zero bridge.** `H⁰(X, ℱ)` as an `A`-module is `Γ(X, ℱ)` as an `A`-module.

Global sections of sheaves of modules on a scheme is a left exact functor
(`Stacks.Cohomology.AffineBase.moduleGlobalSections_preservesFiniteLimits`), so
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` identifies its degree-zero right derived functor
with itself; restriction of scalars along
`Stacks.Cohomology.FormalFunctions.baseRingHom` carries that identification to the `A`-module
structures. -/
public def cohomologyOverBaseZeroIso (F : X.Modules) :
    cohomologyOverBase A f 0 F ≅ globalSectionsOverBase A f F :=
  (ModuleCat.restrictScalars (baseRingHom A f)).mapIso
    ((Functor.rightDerivedZeroIsoSelf (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).app F)

/-- **The degree-zero bridge is natural in the sheaf.** The identification of
`Stacks.Cohomology.FormalFunctions.cohomologyOverBaseZeroIso` carries
`H⁰(X, φ)` to `Γ(X, φ)`.

It is the naturality of `CategoryTheory.Functor.rightDerivedZeroIsoSelf` with restriction of
scalars applied to it. -/
public theorem cohomologyOverBaseZeroIso_naturality {F G : X.Modules} (φ : F ⟶ G) :
    cohomologyOverBaseMap A f 0 φ ≫ (cohomologyOverBaseZeroIso A f G).hom =
      (cohomologyOverBaseZeroIso A f F).hom ≫ globalSectionsOverBaseMap A f φ :=
  ((ModuleCat.restrictScalars (baseRingHom A f)).map_comp _ _).symm.trans
    ((congrArg (ModuleCat.restrictScalars (baseRingHom A f)).map
        ((Functor.rightDerivedZeroIsoSelf
          (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).hom.naturality φ)).trans
      ((ModuleCat.restrictScalars (baseRingHom A f)).map_comp _ _))

/-- Transport of a bound on a kernel across a commutative square whose vertical maps are
isomorphisms: if `u' ∘ g = g' ∘ u` with `u`, `u'` linear equivalences and `ker g ≤ p`, then
`ker g'` is contained in the image of `p` under `u`. -/
private theorem ker_le_map_of_comm {M N M' N' : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module A M] [Module A N] [Module A M'] [Module A N']
    (u : M ≃ₗ[A] M') (u' : N ≃ₗ[A] N') (g : M →ₗ[A] N) (g' : M' →ₗ[A] N')
    (hsq : ∀ x : M, u' (g x) = g' (u x)) {p : Submodule A M} (hp : LinearMap.ker g ≤ p) :
    LinearMap.ker g' ≤ p.map (u : M →ₗ[A] M') := by
  intro x hx
  refine Submodule.mem_map.2 ⟨u.symm x, hp ?_, by simp⟩
  have h0 : u' (g (u.symm x)) = 0 := by
    rw [hsq, u.apply_symm_apply]
    exact hx
  exact (map_eq_zero_iff _ u'.injective).1 h0

/-- The image of `I ^ k · ℳ` under a linear equivalence is `I ^ k` times the target. -/
private theorem map_pow_smul_top (I : Ideal A) (k : ℕ) {M M' : Type u} [AddCommGroup M]
    [AddCommGroup M'] [Module A M] [Module A M'] (u : M ≃ₗ[A] M') :
    (I ^ k • (⊤ : Submodule A M)).map (u : M →ₗ[A] M') = I ^ k • (⊤ : Submodule A M') := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 u.surjective]

/-- **Clause (1) of [Stacks, Tag 02OB] in degree zero, on global sections.** For `A` Noetherian,
`f : X ⟶ Spec A` proper and `ℱ` coherent there is a `c` such that, with `𝓘 = I · 𝒪_X`,

`Ker(Γ(X, ℱ) → Γ(X, ℱ / 𝓘ⁿℱ)) ⊆ Iⁿ⁻ᶜ · Γ(X, ℱ)` for every `n ≥ c`,

as `A`-submodules of `Γ(X, ℱ)`, the `A`-action being restriction of scalars along
`Stacks.Cohomology.FormalFunctions.baseRingHom`.

This is `Stacks.Cohomology.FormalFunctions.ker_cohomology_idealPowerQuotient_le` at `p = 0`
transported across `Stacks.Cohomology.FormalFunctions.cohomologyOverBaseZeroIso`: the kernel of
the transported map is the image of the kernel, and the image of `Iⁿ⁻ᶜ · H⁰(X, ℱ)` under an
isomorphism is `Iⁿ⁻ᶜ · Γ(X, ℱ)`. The constant is the one Stacks 02OB produces, so it serves the
other two clauses as well. -/
public theorem ker_globalSections_idealPowerQuotient_le [IsNoetherianRing A] (I : Ideal A)
    (F : X.Modules) (hX : AlgebraicGeometry.IsProper f)
    (hF : Stacks.SheafOfModules.IsCoherent F) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      LinearMap.ker (globalSectionsOverBaseMap A f
          (cokernel.π (C := X.Modules)
            (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom ≤
        I ^ (n - c) • (⊤ : Submodule A (globalSectionsOverBase A f F)) := by
  obtain ⟨c, hc⟩ := ker_cohomology_idealPowerQuotient_le A f I F 0 hX hF
  refine ⟨c, fun n hn => ?_⟩
  set φ := cokernel.π (C := X.Modules) (idealPowerMultiple (baseIdealSheaf A I f) n F).ι with hφ
  have hsq : ∀ x : cohomologyOverBase A f 0 F,
      (cohomologyOverBaseZeroIso A f _).hom.hom ((cohomologyOverBaseMap A f 0 φ).hom x) =
        (globalSectionsOverBaseMap A f φ).hom ((cohomologyOverBaseZeroIso A f F).hom.hom x) := by
    intro x
    have h := congrArg
      (fun k : cohomologyOverBase A f 0 F ⟶ globalSectionsOverBase A f _ => k.hom x)
      (cohomologyOverBaseZeroIso_naturality A f φ)
    simpa using h
  have hker := ker_le_map_of_comm A (cohomologyOverBaseZeroIso A f F).toLinearEquiv
    (cohomologyOverBaseZeroIso A f _).toLinearEquiv (cohomologyOverBaseMap A f 0 φ).hom
    (globalSectionsOverBaseMap A f φ).hom hsq (hc n hn)
  refine hker.trans (le_of_eq ?_)
  exact map_pow_smul_top A I (n - c) (cohomologyOverBaseZeroIso A f F).toLinearEquiv

end DegreeZero

end Stacks.Cohomology.FormalFunctions

namespace Stacks.Coherent

open Stacks.Algebraization

/-! ### Vanishing in a quotient by a power of an ideal sheaf, read on affine opens -/

/-- **A section lies in `𝒥 ᵏ 𝒢` over an open as soon as the affine opens see it.** Let
`π : 𝒢 ⟶ ℋ` be a morphism of sheaves of modules with `𝒢` quasi-coherent, let `s` be a section of
`𝒢` over an open `U` killed by `π`, and suppose that over every affine open `W ≤ U` a section
killed by `π` lies in `𝒥(W) ᵏ Γ(W, 𝒢)`. Then `s` is a section of the subsheaf `𝒥 ᵏ 𝒢` over `U`.

`Stacks.Algebraization.idealPowerMultiple` is cut out by the submodules `𝒥(W) ᵏ Γ(W, 𝒢)` over the
affine opens (`Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine`), and membership
in a subsheaf is local on them (`Stacks.AlgebraicGeometry.IdealPower.mem_of_forall_affineOpens`),
so only the restrictions of `s` to affine opens are tested; those restrictions are killed by `π`
because `π` commutes with restriction of sections. -/
private theorem mem_idealPowerMultiple_obj_of_affineOpens {Z : Scheme.{u}}
    (K : Z.IdealSheafData) (G : Z.Modules) [G.IsQuasicoherent] {H : Z.Modules} (π : G ⟶ H)
    (k : ℕ) (U : Z.Opens) (s : Γ(G, U)) (hs : π.app U s = 0)
    (hbound : ∀ W : Z.affineOpens, W.1 ≤ U → ∀ x : Γ(G, W.1), π.app W.1 x = 0 →
      x ∈ K.ideal W ^ k • (⊤ : Submodule Γ(Z, W.1) Γ(G, W.1))) :
    s ∈ (idealPowerMultiple K k G).toSubmodule.obj (op U) := by
  refine Stacks.AlgebraicGeometry.IdealPower.mem_of_forall_affineOpens _ s fun W hW => ?_
  rw [idealPowerMultiple_toSubmodule_obj_affine]
  refine hbound W hW _ ?_
  rw [← Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map, hs, map_zero]

/-- **A section of a subsheaf dies in the quotient by it**, on the sections over any open.

The sectionwise kernel of the projection onto the quotient by a submodule is that submodule,
`Stacks.Algebraization.kernelSubmodule_cokernel_π` together with
`Stacks.Algebraization.kernelSubmodule_toSubmodule_obj`; this is that identity read from right to
left. -/
private theorem cokernel_π_app_eq_zero_of_mem {Z : Scheme.{u}} {G : Z.Modules}
    (N : G.Submodule) (U : Z.Opens) (s : Γ(G, U)) (hs : s ∈ N.toSubmodule.obj (op U)) :
    (cokernel.π (C := Z.Modules) N.ι).app U s = 0 := by
  have h1 : s ∈ (kernelSubmodule (cokernel.π (C := Z.Modules) N.ι)).toSubmodule.obj (op U) := by
    rw [kernelSubmodule_cokernel_π]
    exact hs
  rw [kernelSubmodule_toSubmodule_obj] at h1
  exact h1

/-! ### One exponent for a cover of the base -/

section Locality

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The degree-zero Artin–Rees bound for the direct image, localized at an open of the base.**
There is one `c` such that for every pair `n + c ≤ m` the restriction to `V` of the composite

`ker(f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)) ⟶ f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)`

vanishes.

This is `Stacks.Coherent.IsDirectImageAdicBounded` read over `V`, with the quantifier shape
`∃ c, ∀ n m, n + c ≤ m` in place of `∀ n, ∃ m ≥ n`: the constant must not depend on `n`, since
`Stacks.Coherent.isDirectImageAdicBounded_of_affineOpens` replaces finitely many such constants
by their maximum and then chooses `m` from `n` and that maximum. Over an affine open it is
clause (1) of Stacks 02OB in degree zero — the bound `Iᵐ⁻ᶜ` of
`Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le` is where the
constant comes from. -/
public def IsDirectImageAdicBoundedOn (V : Y.Opens) : Prop :=
  ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
    (Scheme.Modules.restrictFunctor V.ι).map
      (kernel.ι (C := Y.Modules)
          ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) ≫
        completionProjection Y J (properPushforwardCoherent f F) n) = 0

/-- **The localized bound is a statement about sections over affine opens.** If there is one `c`
such that for every pair `n + c ≤ m` and every affine open `W ≤ V` a section of `f_*𝓕` over `W`
killed by `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` lies in `𝒥(W) ⁿ⁺¹ Γ(W, f_*𝓕)`, then
`Stacks.Coherent.IsDirectImageAdicBoundedOn f J F V` holds.

The hypothesis is clause (1) of Stacks 02OB in degree zero, written out on the sections over an
affine open: the kernel of `Γ(W, f_*𝓕) → Γ(W, f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕))` is contained in
`𝒥(W) ⁿ⁺¹ Γ(W, f_*𝓕)`. It is what
`Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le` produces over an
affine base, modulo the identification of `Γ(W, f_*𝓕)` with `Γ(f⁻¹W, 𝓕)`
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`, by `rfl`) and of the restricted data
with the data of the restricted morphism
(`CompletionProper/DirectImageRestrictOpen.lean`).

What this lemma supplies is the sheaf-theoretic plumbing on the base, and nothing else. The
projection `f_*𝓕 ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)` is a cokernel in `Y.Modules`, so its sections over a
general open are not a quotient of the sections; on an *affine* open they are, by
`Stacks.Algebraization.cokernel_π_idealPowerMultiple_app_eq_zero_iff`, and the affine opens form
a basis, so separatedness of the quotient sheaf
(`Stacks.AlgebraicGeometry.IdealPower.eq_zero_of_locally_zero`) promotes the vanishing from them
to every open contained in `V`. That is exactly the restriction of the composite to `V`
(`Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctor_map_eq_of_restrictHomSection`).

Note that the hypothesis quantifies over **every** affine open contained in `V`, with one
constant: that single constant for all of them, rather than one per affine open, is the whole of
what is still missing, and it is the flat base change of the Artin–Rees constant along an open
immersion of affines that the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicArtinRees.lean` record as absent. -/
public theorem isDirectImageAdicBoundedOn_of_forall_affineOpens (V : Y.Opens) (c : ℕ)
    (h : ∀ n m : ℕ, n + c ≤ m → ∀ W : Y.affineOpens, W.1 ≤ V →
      ∀ s : Γ((Scheme.Modules.pushforward f).obj F.obj, W.1),
        ((Scheme.Modules.pushforward f).map
            (completionProjection X (J.comap f) F m)).app W.1 s = 0 →
          s ∈ J.ideal W ^ (n + 1) •
            (⊤ : Submodule Γ(Y, W.1) Γ((Scheme.Modules.pushforward f).obj F.obj, W.1))) :
    IsDirectImageAdicBoundedOn f J F V := by
  have hcoh : ((Scheme.Modules.pushforward f).obj F.obj).IsCoherent :=
    (properPushforwardCoherent f F).property
  have hqc : ((Scheme.Modules.pushforward f).obj F.obj).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((Scheme.Modules.pushforward f).obj F.obj)).1
  refine ⟨c, fun n m hnm => ?_⟩
  refine Eq.trans ?_ (Functor.map_zero (Scheme.Modules.restrictFunctor V.ι) _ _)
  refine Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctor_map_eq_of_restrictHomSection
    fun U hU t => ?_
  rw [Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection_restrictFunctor_map,
    Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection_restrictFunctor_map,
    Scheme.Modules.Hom.zero_app]
  -- the kernel inclusion is killed by the morphism it is the kernel of
  have hs0 : ((Scheme.Modules.pushforward f).map
        (completionProjection X (J.comap f) F m)).app U
      ((kernel.ι (C := Y.Modules) ((Scheme.Modules.pushforward f).map
        (completionProjection X (J.comap f) F m))).app U t) = 0 := by
    have hk := kernel.condition (C := Y.Modules)
      ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m))
    have hrfl : ((Scheme.Modules.pushforward f).map
          (completionProjection X (J.comap f) F m)).app U
        ((kernel.ι (C := Y.Modules) ((Scheme.Modules.pushforward f).map
          (completionProjection X (J.comap f) F m))).app U t) =
      Scheme.Modules.Hom.app (kernel.ι (C := Y.Modules) ((Scheme.Modules.pushforward f).map
            (completionProjection X (J.comap f) F m)) ≫
          (Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) U t := rfl
    rw [hrfl, hk]
    simp only [Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]
  -- so the affine-open hypothesis applies to it, and the quotient projection kills it
  have hmem := mem_idealPowerMultiple_obj_of_affineOpens J
    ((Scheme.Modules.pushforward f).obj F.obj)
    ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) (n + 1) U
    ((kernel.ι (C := Y.Modules) ((Scheme.Modules.pushforward f).map
      (completionProjection X (J.comap f) F m))).app U t) hs0
    fun W hW x hx => h n m hnm W (le_trans hW hU) x hx
  have hck := cokernel_π_app_eq_zero_of_mem
    (idealPowerMultiple J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj)) U _ hmem
  -- and the completion projection is that quotient projection up to an isomorphism
  have hrfl : Scheme.Modules.Hom.app (kernel.ι (C := Y.Modules)
          ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) ≫
        completionProjection Y J (properPushforwardCoherent f F) n) U t =
      (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n).symm).app U
        ((cokernel.π (C := Y.Modules)
            (idealPowerMultiple J (n + 1)
              ((Scheme.Modules.pushforward f).obj F.obj)).ι).app U
          ((kernel.ι (C := Y.Modules) ((Scheme.Modules.pushforward f).map
            (completionProjection X (J.comap f) F m))).app U t)) := rfl
  rw [hrfl, hck]
  simp only [AddCommGrpCat.zero_apply]
  exact map_zero _

/-- **The localized bound over every affine open of the base gives the bound.** If for every
affine open `V` of `Y` there is one constant `c` making the restriction to `V` of

`ker(f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)) ⟶ (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)`

vanish whenever `n + c ≤ m`, then `Stacks.Coherent.IsDirectImageAdicBounded` holds.

This is the uniformity step that the module docstring of
`CompletionProper/DirectImageLimitComparison.lean` names as the real cost of passing from the
affine-base statement of Stacks 02OB to a containment of subsheaves on a general Noetherian base:
the Artin–Rees constant depends on the affine open, and one constant must serve a whole cover.
The affine opens of a scheme form a basis of its topology
(`AlgebraicGeometry.Scheme.isBasis_affineOpens`), so a quasi-compact `Y` is covered by finitely
many of them (`TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact`); `Finite.exists_le`
bounds their finitely many constants by one `N`, and `m = n + N` then works over every member.
Equality of morphisms of sheaves of modules being local
(`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover`), the composite vanishes.

Only `[CompactSpace Y]` is used of the hypotheses on `Y`, as in
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_affineOpens`, whose argument this
is; `[IsNoetherian Y]` supplies it. There is no finiteness hypothesis at the call site: the
hypothesis is taken over every affine open and the finite subfamily is produced here. -/
public theorem isDirectImageAdicBounded_of_affineOpens
    (h : ∀ V : Y.affineOpens, IsDirectImageAdicBoundedOn f J F V.1) :
    IsDirectImageAdicBounded f J F := by
  have hbasis : TopologicalSpace.Opens.IsBasis (Set.range fun V : Y.affineOpens => V.1) := by
    have heq : Set.range (fun V : Y.affineOpens => V.1) = Y.affineOpens := by
      ext W
      exact ⟨fun ⟨V, hV⟩ => hV ▸ V.property, fun hW => ⟨⟨W, hW⟩, rfl⟩⟩
    rw [heq]
    exact Y.isBasis_affineOpens
  obtain ⟨κ, hκ, a, hcov⟩ := hbasis.exists_iSup_eq_of_isCompact (⊤ : Y.Opens) isCompact_univ
  have : Finite κ := hκ
  obtain ⟨N, hN⟩ := Finite.exists_le fun k : κ => (h (a k)).choose
  have hmem : ∀ x : Y, ∃ k : κ, x ∈ (a k).1 := by
    intro x
    have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [hcov] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  intro n
  refine ⟨n + N, Nat.le_add_right n N, ?_⟩
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover
    (fun k : κ => (a k).1) hmem fun k => ?_
  refine ((h (a k)).choose_spec n (n + N) (Nat.add_le_add_left (hN k) n)).trans ?_
  exact (Functor.map_zero _ _ _).symm

/-- **Stacks 02OC in degree zero, in the relative sheaf form, from the localized Artin–Rees
bound.** Granted the localized bound over every affine open of the base, the comparison
`δ : (f_*𝓕) ^∧ ⟶ f_*(𝓕 ^∧)` induces a monomorphism on inverse limits.

This is `Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem` with its hypothesis
replaced by the form in which Stacks 02OB can supply it, affine open by affine open, through
`Stacks.Coherent.isDirectImageAdicBounded_of_affineOpens`. -/
public theorem mono_limMap_directImageQuotientComparisonSystem_of_affineOpens
    (h : ∀ V : Y.affineOpens, IsDirectImageAdicBoundedOn f J F V.1) :
    Mono (limMap (C := Y.Modules) (directImageQuotientComparisonSystem f J F)) :=
  mono_limMap_directImageQuotientComparisonSystem f J F
    (isDirectImageAdicBounded_of_affineOpens f J F h)

/-- **The uniqueness clause of the proof of Stacks 088B, from the localized Artin–Rees bound.**
Two morphisms out of a completion `𝒜 ^∧` with the same composite with
`Stacks.Coherent.directImageQuotientComparisonSystem` are equal, granted the localized bound over
every affine open of the base. -/
public theorem eq_of_comp_directImageQuotientComparisonSystem_eq_of_affineOpens
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (h : ∀ V : Y.affineOpens, IsDirectImageAdicBoundedOn f J F V.1)
    {u v : ((completionFunctor Y J).obj 𝒜).obj ⟶
      ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj}
    (hcomp : u ≫ directImageQuotientComparisonSystem f J F =
      v ≫ directImageQuotientComparisonSystem f J F) : u = v :=
  eq_of_comp_directImageQuotientComparisonSystem_eq_of_adicBounded f J F 𝒜
    (isDirectImageAdicBounded_of_affineOpens f J F h) hcomp

end Locality

end Stacks.Coherent

end
