module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageAdicBound

/-!
# Flat base change for the sections of a quasi-coherent module along an inclusion of affine opens

`CompletionProper/DirectImageAdicBound.lean` reduces `Stacks.Coherent.IsDirectImageAdicBounded` —
clause (1) of Stacks 02OB in degree zero, at the relative level, which is what stands between the
library and Stacks 02OC relative, the uniqueness clause of Stacks 088B, and Stacks 088E — to the
single hypothesis `h` of
`Stacks.Coherent.isDirectImageAdicBoundedOn_of_forall_affineOpens`: the containment

`Ker(Γ(W, f_*𝓕) → Γ(W, f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕))) ⊆ 𝒥(W) ⁿ⁺¹ Γ(W, f_*𝓕)` for `n + c ≤ m`,

over **every** affine open `W ≤ V`, **with one constant `c` for all of them**. Over a single
affine open the containment is the affine-base statement of Stacks 02OB, available as
`Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le` applied to the proper
morphism `f ∣_ W` onto an affine scheme, with the constant that Stacks 02OB produces for `f ∣_ W`.
That constant depends on `W`; what makes one constant serve a whole family of affine opens is the
flat base change this file supplies, which the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicArtinRees.lean` record as absent — the reason
that file fixes a finite affine cover in advance and concludes only about the sections over `⊤`.

The input is nowhere near as deep as the uniformity it buys. An **open immersion is flat**, so for
affine opens `W' ≤ W` of a scheme the restriction map `Γ(W, 𝒪) ⟶ Γ(W', 𝒪)` is flat; and for a
quasi-coherent module `F` the restriction `Γ(W, F) ⟶ Γ(W', F)` exhibits `Γ(W', F)` as
`Γ(W, F) ⊗_{Γ(W,𝒪)} Γ(W', 𝒪)`. Both of these are already available and neither is reproved here:
the first is Mathlib's morphism property `AlgebraicGeometry.Flat` read on sections
(`AlgebraicGeometry.Flat.flat_appLE`) at the identity morphism, and the second is
`AlgebraicGeometry.isBaseChange_restrict_of_isAffineOpen` of
`StacksFrontier/AlgebraicGeometry/AffineOpenSectionsBaseChange/Basic.lean`. What this file adds is
the consequence: flatness makes kernels base change, the restriction of `𝒥(W)` generates `𝒥(W')`
(`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`), and so a containment of a kernel in
`𝒥(W) ᵏ Γ(W, 𝓖)` over `W` forces the same containment over every affine `W' ≤ W` with the same
exponent.

## Main results

* `Stacks.AffineOpenSectionsBaseChange.ker_le_span_image_of_flat` and
  `Stacks.AffineOpenSectionsBaseChange.span_image_pow_smul_le` — **the two module facts.** For a
  flat algebra `S` over `R`, a map of base changes has kernel generated over `S` by the
  restrictions of the kernel upstairs, and the `S`-span of the image of `Iᵏ M` is contained in
  `(I S)ᵏ N`. `Stacks.AffineOpenSectionsBaseChange.mem_pow_smul_of_flat` is their composite, in
  the pointwise shape the geometric caller has.
* `Stacks.AffineOpenSectionsBaseChange.flat_presheafMap_of_isAffineOpen` and
  `Stacks.AffineOpenSectionsBaseChange.flat_of_isAffineOpen` — **flatness of the restriction map
  between affine opens**, as a flat ring map and as a flat module.
* `Stacks.AffineOpenSectionsBaseChange.mem_idealPow_smul_of_le_of_affineOpens` — **the transfer.**
  For `φ : 𝒢 ⟶ ℋ` a morphism of quasi-coherent modules and `W' ≤ W` affine opens, a bound
  `Ker(φ_W) ⊆ K(W) ᵏ Γ(W, 𝒢)` gives `Ker(φ_{W'}) ⊆ K(W') ᵏ Γ(W', 𝒢)`, with the same `k`.
* `Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBoundedOn_of_affineOpen_self` — **the
  uniform constant.** The hypothesis `h` of
  `Stacks.Coherent.isDirectImageAdicBoundedOn_of_forall_affineOpens`, over an affine open `V` of
  the base, follows from its own special case `W = V`.
* `Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self` and
  `mono_limMap_directImageQuotientComparisonSystem_of_affineOpens_self` in the same namespace
  — `Stacks.Coherent.IsDirectImageAdicBounded` and Stacks 02OC in degree zero in the relative
  sheaf form, from clause (1) of Stacks 02OB read on the sections over each affine open of the
  base separately, each with its own constant.

## What is still a hypothesis, and why

Exactly one thing: the sections bound over a **single** affine open `V` of the base, which is the
hypothesis of
`Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self`. That is the
affine-base statement of Stacks 02OB in degree zero, already proved as
`Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le`; what remains is to
move it across the identifications of `f ∣_ V : f ⁻¹ V ⟶ V` with a proper morphism to an affine
scheme (`AlgebraicGeometry.IsProper.instMorphismRestrict`,
`AlgebraicGeometry.IsAffineOpen.isoSpec`), of the restricted ideal sheaf
(`Stacks.Coherent.comap_comap_morphismRestrict`), of the restricted comparison
(`Stacks.Coherent.directImageQuotientComparison_restrict`, both in
`CompletionProper/DirectImageRestrictOpen.lean`) and of `Γ(V, f_*𝓕)` with `Γ(f ⁻¹ V, 𝓕)`
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`, by `rfl`). No uniformity is involved in
that step, and nothing in it is missing from the tree.

No `@[stacks]` attribute is attached. Flatness of an open immersion and base change of the
sections of a quasi-coherent module are Mathlib's and are registered where they live; the
transfer and the uniform constant are steps in the proof of Stacks 02OB at the relative level,
whose tag registration is on
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_isProper`
(`CompletionProper/ArtinReesChain.lean`).

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.AffineOpenSectionsBaseChange

/-! ### Flat base change of kernels, as modules -/

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Flat base change of a kernel, in span form.** Let `S` be a flat `R`-algebra, let
`ρ : M ⟶ N` and `σ : P ⟶ Q` exhibit `N` and `Q` as the base changes of `M` and `P` to `S`, and
let `ψ : N ⟶ Q` be an `S`-linear map agreeing with an `R`-linear `φ : M ⟶ P` under `ρ` and `σ`.
Then the kernel of `ψ` is generated over `S` by the image under `ρ` of the kernel of `φ`.

Flatness enters once: `S ⊗[R] -` applied to the exact sequence `ker φ ⟶ M ⟶ P` is exact, so an
element of `S ⊗[R] M` killed by `S ⊗[R] φ` comes from `S ⊗[R] ker φ`, and the elementary tensors
of the latter are exactly the `s • ρ k` with `k ∈ ker φ`. -/
public theorem ker_le_span_image_of_flat [Module.Flat R S]
    {M N P Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    {ρ : M →ₗ[R] N} (hρ : IsBaseChange S ρ) {σ : P →ₗ[R] Q} (hσ : IsBaseChange S σ)
    (φ : M →ₗ[R] P) (ψ : N →ₗ[S] Q) (hcomm : ∀ m : M, ψ (ρ m) = σ (φ m)) :
    LinearMap.ker ψ ≤ Submodule.span S (ρ '' (LinearMap.ker φ : Set M)) := by
  have hsq : ∀ x : S ⊗[R] M, hσ.equiv (LinearMap.lTensor S φ x) = ψ (hρ.equiv x) := by
    intro x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro s m
      rw [LinearMap.lTensor_tmul, hσ.equiv_tmul, hρ.equiv_tmul, map_smul, hcomm m]
    · intro a b ha hb
      rw [map_add, map_add, map_add, map_add, ha, hb]
  have hexact : Function.Exact
      (LinearMap.lTensor S (Submodule.subtype (LinearMap.ker φ))) (LinearMap.lTensor S φ) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map φ)
  have key : ∀ z : S ⊗[R] (LinearMap.ker φ),
      hρ.equiv (LinearMap.lTensor S (Submodule.subtype (LinearMap.ker φ)) z) ∈
        Submodule.span S (ρ '' (LinearMap.ker φ : Set M)) := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro s w
      rw [LinearMap.lTensor_tmul, hρ.equiv_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w.1, w.2, rfl⟩)
    · intro a b ha hb
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  intro t ht
  have h0 : LinearMap.lTensor S φ (hρ.equiv.symm t) = 0 := by
    refine hσ.equiv.injective ?_
    rwa [hsq, hρ.equiv.apply_symm_apply, map_zero]
  obtain ⟨z, hz⟩ := (hexact _).mp h0
  have h1 := key z
  rwa [hz, hρ.equiv.apply_symm_apply] at h1

/-- **The submodule `Iᵏ M` base changes.** The `S`-span of the image under a base change
`ρ : M ⟶ N` of `Iᵏ · M` lies in `(I S)ᵏ · N`. -/
public theorem span_image_pow_smul_le
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (ρ : M →ₗ[R] N) (I : Ideal R) (k : ℕ) :
    Submodule.span S (ρ '' ((I ^ k • (⊤ : Submodule R M) : Submodule R M) : Set M)) ≤
      (I.map (algebraMap R S)) ^ k • (⊤ : Submodule S N) := by
  rw [Submodule.span_le]
  rintro n ⟨m, hm, rfl⟩
  refine Submodule.smul_induction_on hm (fun a ha m' _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, ← algebraMap_smul S a (ρ m')]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **Flat base change of an ideal-power bound on a kernel.** Let `S` be a flat `R`-algebra, let
`ρ : M ⟶ N` and `σ : P ⟶ Q` exhibit `N` and `Q` as the base changes of `M` and `P` to `S`, and let
`ψ : N ⟶ Q` be an `S`-linear map agreeing with an `R`-linear `φ : M ⟶ P` under `ρ` and `σ`. If
everything killed by `φ` lies in `Iᵏ M`, then everything killed by `ψ` lies in `(I S)ᵏ N`.

This is `Stacks.AffineOpenSectionsBaseChange.ker_le_span_image_of_flat` followed by
`Stacks.AffineOpenSectionsBaseChange.span_image_pow_smul_le`, stated with the bound and the
conclusion as implications between equations rather than as containments of kernels: that is the
shape in which the geometric caller has them, and `LinearMap.ker` of a map between the section
types of a sheaf of modules on a scheme is a shape whose module structure instance search does
not find. -/
public theorem mem_pow_smul_of_flat [Module.Flat R S]
    {M N P Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    {ρ : M →ₗ[R] N} (hρ : IsBaseChange S ρ) {σ : P →ₗ[R] Q} (hσ : IsBaseChange S σ)
    (φ : M →ₗ[R] P) (ψ : N →ₗ[S] Q) (hcomm : ∀ m : M, ψ (ρ m) = σ (φ m))
    (I : Ideal R) (k : ℕ)
    (hbound : ∀ m : M, φ m = 0 → m ∈ I ^ k • (⊤ : Submodule R M))
    (t : N) (ht : ψ t = 0) :
    t ∈ (I.map (algebraMap R S)) ^ k • (⊤ : Submodule S N) := by
  have h2 : (LinearMap.ker φ : Set M) ⊆
      ((I ^ k • (⊤ : Submodule R M) : Submodule R M) : Set M) :=
    fun m hm => hbound m (LinearMap.mem_ker.mp hm)
  exact span_image_pow_smul_le ρ I k (Submodule.span_mono (Set.image_mono h2)
    (ker_le_span_image_of_flat hρ hσ φ ψ hcomm (LinearMap.mem_ker.mpr ht)))

end Algebra

/-! ### An open immersion is flat: the restriction maps between affine opens -/

/-- **The restriction map between affine opens of a scheme is flat.** For affine opens `W' ≤ W`
of a scheme `Z` the ring map `Γ(Z, W) ⟶ Γ(Z, W')` is flat.

Nothing is proved here: the identity of `Z` is an open immersion, hence flat
(`AlgebraicGeometry.Flat`, from `AlgebraicGeometry.HasRingHomProperty.of_isOpenImmersion`), and
flatness of a morphism of schemes *is* flatness of the maps `Γ(Z, U) ⟶ Γ(Z, V)` it induces on
sections over affine opens `V ≤ f ⁻¹ᵁ U` (`AlgebraicGeometry.Flat.flat_appLE`). For the identity
morphism `appLE` is restriction of sections, which is
`AlgebraicGeometry.Scheme.Hom.appLE_id`. -/
public theorem flat_presheafMap_of_isAffineOpen {Z : Scheme.{u}} {W W' : Z.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W) :
    (Z.presheaf.map (homOfLE hle).op).hom.Flat := by
  have hle' : W' ≤ (𝟙 Z :) ⁻¹ᵁ W := by simpa using hle
  have h := AlgebraicGeometry.Flat.flat_appLE (𝟙 Z) hW hW' hle'
  rwa [AlgebraicGeometry.Scheme.Hom.appLE_id W W' hle' hle] at h

/-- **`Γ(Z, W')` is a flat `Γ(Z, W)`-module for affine opens `W' ≤ W`.** This is
`Stacks.AffineOpenSectionsBaseChange.flat_presheafMap_of_isAffineOpen` read as flatness of a
module, for an algebra structure whose structure map is the restriction map. -/
public theorem flat_of_isAffineOpen {Z : Scheme.{u}} {W W' : Z.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W)
    [Algebra Γ(Z, W) Γ(Z, W')]
    (halg : ∀ r : Γ(Z, W), algebraMap Γ(Z, W) Γ(Z, W') r =
      (Z.presheaf.map (homOfLE hle).op).hom r) :
    Module.Flat Γ(Z, W) Γ(Z, W') := by
  rw [← RingHom.flat_algebraMap_iff,
    show (algebraMap Γ(Z, W) Γ(Z, W')) = (Z.presheaf.map (homOfLE hle).op).hom from
      RingHom.ext halg]
  exact flat_presheafMap_of_isAffineOpen hW hW' hle

/-! ### The transfer of an ideal-power bound to a smaller affine open -/

/-- **An ideal-power bound on the sections over an affine open transfers to every smaller affine
open, with the same exponent.** Let `φ : 𝒢 ⟶ ℋ` be a morphism of quasi-coherent modules on a
scheme `Z`, let `K` be a quasi-coherent ideal sheaf and let `W' ≤ W` be affine opens. If every
section of `𝒢` over `W` killed by `φ` lies in `K(W)ᵏ Γ(W, 𝒢)`, then every section of `𝒢` over `W'`
killed by `φ` lies in `K(W')ᵏ Γ(W', 𝒢)`.

This is the flat base change that makes one Artin–Rees constant serve a whole family of affine
opens. The restriction map `Γ(Z, W) ⟶ Γ(Z, W')` is flat
(`Stacks.AffineOpenSectionsBaseChange.flat_of_isAffineOpen`), restriction exhibits the sections
over `W'` as the base change of the sections over `W` for both `𝒢` and `ℋ`
(`AlgebraicGeometry.isBaseChange_restrict_of_isAffineOpen`), so the kernel of `φ` over `W'` is
generated by the restrictions of the kernel over `W`
(`Stacks.AffineOpenSectionsBaseChange.ker_le_span_image_of_flat`); the restrictions of
`K(W)ᵏ Γ(W, 𝒢)` generate `K(W')ᵏ Γ(W', 𝒢)` because `K(W)` generates `K(W')`
(`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`), which is
`Stacks.AffineOpenSectionsBaseChange.span_image_pow_smul_le`. -/
public theorem mem_idealPow_smul_of_le_of_affineOpens {Z : Scheme.{u}} (K : Z.IdealSheafData)
    {G H : Z.Modules} [G.IsQuasicoherent] [H.IsQuasicoherent] (φ : G ⟶ H) (k : ℕ)
    (W W' : Z.affineOpens) (hle : W'.1 ≤ W.1)
    (hbound : ∀ s : Γ(G, W.1), φ.app W.1 s = 0 →
      s ∈ K.ideal W ^ k • (⊤ : Submodule Γ(Z, W.1) Γ(G, W.1)))
    (t : Γ(G, W'.1)) (ht : φ.app W'.1 t = 0) :
    t ∈ K.ideal W' ^ k • (⊤ : Submodule Γ(Z, W'.1) Γ(G, W'.1)) := by
  let alg : Algebra Γ(Z, W.1) Γ(Z, W'.1) :=
    (Z.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have halg : ∀ r : Γ(Z, W.1),
      algebraMap Γ(Z, W.1) Γ(Z, W'.1) r = Z.presheaf.map (homOfLE hle).op r := fun _ => rfl
  have hflat : Module.Flat Γ(Z, W.1) Γ(Z, W'.1) :=
    flat_of_isAffineOpen W.2 W'.2 hle halg
  let _ : ∀ M : Z.Modules, Module Γ(Z, W.1) Γ(M, W'.1) := fun M =>
    Module.compHom _ (Z.presheaf.map (homOfLE hle).op).hom
  have _ : ∀ M : Z.Modules, IsScalarTower Γ(Z, W.1) Γ(Z, W'.1) Γ(M, W'.1) := fun M =>
    ⟨fun x y z => mul_smul ((Z.presheaf.map (homOfLE hle).op).hom x) y z⟩
  let ρ (M : Z.Modules) : Γ(M, W.1) →ₗ[Γ(Z, W.1)] Γ(M, W'.1) :=
    { toFun := fun b => M.presheaf.map (homOfLE hle).op b
      map_add' := fun b c => map_add _ _ _
      map_smul' := fun r b => Scheme.Modules.map_smul M (homOfLE hle) r b }
  let app (U : Z.Opens) : Γ(G, U) →ₗ[Γ(Z, U)] Γ(H, U) :=
    { toFun := fun x => φ.app U x
      map_add' := fun x y => map_add _ _ _
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul φ r x }
  have hbc (M : Z.Modules) [M.IsQuasicoherent] : IsBaseChange Γ(Z, W'.1) (ρ M) :=
    isBaseChange_restrict_of_isAffineOpen M W.2 W'.2 hle halg (ρ M) fun _ => rfl
  have hcomm : ∀ m : Γ(G, W.1), app W'.1 (ρ G m) = ρ H (app W.1 m) := fun m =>
    (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map φ hle m).symm
  have hideal : (K.ideal W).map (algebraMap Γ(Z, W.1) Γ(Z, W'.1)) = K.ideal W' := by
    rw [show (algebraMap Γ(Z, W.1) Γ(Z, W'.1)) = (Z.presheaf.map (homOfLE hle).op).hom from
      RingHom.ext halg]
    exact K.map_ideal hle
  rw [← hideal]
  exact mem_pow_smul_of_flat (hbc G) (hbc H) (app W.1) (app W'.1) hcomm (K.ideal W) k
    (fun m hm => hbound m hm) t ht

/-! ### One Artin–Rees constant for all the affine opens contained in an affine open -/

section Uniform

open Stacks.Algebraization Stacks.Coherent

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **One constant for all the affine opens contained in an affine open.** If, over an affine
open `V` of the base alone, every section of `f_*𝓕` killed by `f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` lies in
`𝒥(V) ⁿ⁺¹ Γ(V, f_*𝓕)` whenever `n + c ≤ m`, then the same holds over **every** affine open
`W ≤ V`, with the same `c`, and therefore
`Stacks.Coherent.IsDirectImageAdicBoundedOn f J F V` holds.

This is the step that the module docstring of
`CompletionProper/DirectImageAdicBound.lean` and the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicArtinRees.lean` record as missing: the
Artin–Rees constant of Stacks 02OB depends on the affine open it is read over, and what makes one
constant serve a whole family is that `Γ(V, 𝒪_Y) ⟶ Γ(W, 𝒪_Y)` is flat for `W ≤ V` an inclusion of
affine opens, so that the kernel of a map of quasi-coherent modules and the submodule
`𝒥(V) ⁿ⁺¹ Γ(V, f_*𝓕)` both base change. That is
`Stacks.AffineOpenSectionsBaseChange.mem_idealPow_smul_of_le_of_affineOpens`, and the passage from
the resulting family to the localized bound is
`Stacks.Coherent.isDirectImageAdicBoundedOn_of_forall_affineOpens`.

Both modules the transfer is applied to are quasi-coherent: `f_*𝓕` is coherent because `f` is
proper (`Stacks.Coherent.properPushforwardCoherent`), and so is the direct image of the `m`-th
term of the completion, that term being coherent by the first clause of
`Stacks.Coherent.IsCoherentAdicSystem` and the direct image of a coherent module along a proper
morphism being coherent (`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`);
coherence gives quasi-coherence by
`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent`. -/
public theorem isDirectImageAdicBoundedOn_of_affineOpen_self (V : Y.affineOpens) (c : ℕ)
    (h : ∀ n m : ℕ, n + c ≤ m →
      ∀ s : Γ((Scheme.Modules.pushforward f).obj F.obj, V.1),
        ((Scheme.Modules.pushforward f).map
            (completionProjection X (J.comap f) F m)).app V.1 s = 0 →
          s ∈ J.ideal V ^ (n + 1) •
            (⊤ : Submodule Γ(Y, V.1) Γ((Scheme.Modules.pushforward f).obj F.obj, V.1))) :
    IsDirectImageAdicBoundedOn f J F V.1 := by
  have hcoh : ((Scheme.Modules.pushforward f).obj F.obj).IsCoherent :=
    (properPushforwardCoherent f F).property
  have hqc : ((Scheme.Modules.pushforward f).obj F.obj).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((Scheme.Modules.pushforward f).obj F.obj)).1
  refine isDirectImageAdicBoundedOn_of_forall_affineOpens f J F V.1 c
    fun n m hnm W hWV s hs => ?_
  have hcohm : (((completionFunctor X (J.comap f)).obj F).obj.obj (op m)).IsCoherent :=
    ((completionFunctor X (J.comap f)).obj F).property.1 m
  have hcohH : ((Scheme.Modules.pushforward f).obj
      (((completionFunctor X (J.comap f)).obj F).obj.obj (op m))).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _
  have hqcH : ((Scheme.Modules.pushforward f).obj
      (((completionFunctor X (J.comap f)).obj F).obj.obj (op m))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  exact mem_idealPow_smul_of_le_of_affineOpens J
    ((Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F m)) (n + 1)
    V W hWV (h n m hnm) s hs

/-- **The degree-zero Artin–Rees bound for the direct image, from the bound over each affine open
of the base separately.** If over every affine open `V` of `Y` there is a constant `c` — depending
on `V`, with no uniformity over the affine opens contained in `V` — making the sections bound of
clause (1) of Stacks 02OB hold over `V` itself, then `Stacks.Coherent.IsDirectImageAdicBounded`
holds.

This is `Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBoundedOn_of_affineOpen_self`
followed by `Stacks.Coherent.isDirectImageAdicBounded_of_affineOpens`: the flat base change
supplies the uniformity inside each affine open, and quasi-compactness of `Y` with the maximum of
finitely many constants supplies it across a cover. The hypothesis is clause (1) of Stacks 02OB in
degree zero read on the global sections of the restriction `f ∣_ V` over an **affine** base, which
is the shape `Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le`
produces. -/
public theorem isDirectImageAdicBounded_of_affineOpens_self
    (h : ∀ V : Y.affineOpens, ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      ∀ s : Γ((Scheme.Modules.pushforward f).obj F.obj, V.1),
        ((Scheme.Modules.pushforward f).map
            (completionProjection X (J.comap f) F m)).app V.1 s = 0 →
          s ∈ J.ideal V ^ (n + 1) •
            (⊤ : Submodule Γ(Y, V.1) Γ((Scheme.Modules.pushforward f).obj F.obj, V.1))) :
    IsDirectImageAdicBounded f J F :=
  isDirectImageAdicBounded_of_affineOpens f J F fun V =>
    isDirectImageAdicBoundedOn_of_affineOpen_self f J F V (h V).choose (h V).choose_spec

/-- **Stacks 02OC in degree zero, in the relative sheaf form, from the bound over each affine open
of the base separately.** The comparison `δ : (f_*𝓕) ^∧ ⟶ f_*(𝓕 ^∧)` induces a monomorphism on
inverse limits as soon as clause (1) of Stacks 02OB holds on the sections over each affine open of
the base, with a constant that may depend on that affine open.

This is `Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem` with its hypothesis
discharged by
`Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self`. -/
public theorem mono_limMap_directImageQuotientComparisonSystem_of_affineOpens_self
    (h : ∀ V : Y.affineOpens, ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      ∀ s : Γ((Scheme.Modules.pushforward f).obj F.obj, V.1),
        ((Scheme.Modules.pushforward f).map
            (completionProjection X (J.comap f) F m)).app V.1 s = 0 →
          s ∈ J.ideal V ^ (n + 1) •
            (⊤ : Submodule Γ(Y, V.1) Γ((Scheme.Modules.pushforward f).obj F.obj, V.1))) :
    Mono (limMap (C := Y.Modules) (directImageQuotientComparisonSystem f J F)) :=
  mono_limMap_directImageQuotientComparisonSystem f J F
    (isDirectImageAdicBounded_of_affineOpens_self f J F h)

end Uniform

end Stacks.AffineOpenSectionsBaseChange

end
