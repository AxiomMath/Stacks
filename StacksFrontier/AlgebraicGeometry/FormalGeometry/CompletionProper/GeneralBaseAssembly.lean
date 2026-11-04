module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDualGlobal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicBoundAffineChart
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AnnihilationLocality
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceSeparated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportAlgebraization
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 088B at a general base: the overlap hypothesis of the glueing is discharged

Let `π : X' ⟶ X` be a proper morphism of Noetherian schemes, let `𝒥, 𝒦 ⊆ 𝒪_X` be quasi-coherent
sheaves of ideals, let `(𝒢_n)` be an object of `Coh(X, 𝒥)`, let `𝓕` be a coherent
`𝒪_{X'}`-module and `β : π^*(𝒢_n) ≅ 𝓕 ^∧`. The glueing of [Stacks, Tag 088B] over an affine open
cover of the base,
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover`, carries
four binders: the local solutions `ψ`, their restricted characterization `hchar`, their
annihilation `hann`, and the **overlap agreement** `hψ`.

This file removes `hψ`. It is not an extra hypothesis on the local solutions: two morphisms of
the restricted systems which satisfy the restricted characterization over two opens of the base
automatically have the same action on the sections over any open contained in both.

## What makes the overlap agreement free

The source says "`α` is unique, so we may work locally". The uniqueness clause the library had,
`Stacks.AdicBoundAffineChart.eq_of_comp_directImageQuotientComparisonSystem_eq`, is for morphisms
out of a **completion** `𝒜 ^∧`: it goes through
`Stacks.Algebraization.completionSystemHom_ext`, so it cannot be applied to `(𝒢_n)` itself, and
over an open of the base `(𝒢_n)` is not a completion — that failure is exactly the one
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/AffineExistenceDescent.lean`
exhibits.

What is used here instead is the *pro-zero* form of the degree-zero Artin–Rees bound, which needs
no completion anywhere. By
`Stacks.Coherent.kernel_directImageQuotientComparisonApp_comp_map_eq_zero` the kernel of `δ_m` is
killed by the transition map down to an earlier level `k`, and by
`Stacks.AdicBoundAffineChart.isDirectImageAdicBounded` such an `m` exists for every `k` with no
hypothesis at all. Since the transition maps of a coherent adic system are epimorphisms
(`Stacks.Coherent.IsCoherentAdicSystem.epi_map`), a morphism `d : (𝒢_n) ⟶ (π_*𝓕) ^∧` with
`d ≫ δ = 0` vanishes: at level `k` it is computed from level `m`, where it factors through
`ker δ_m`, which the transition kills. Nothing in that argument is global, and both inputs
survive restriction to an open `W ⊆ X`: `AlgebraicGeometry.Scheme.Modules.restrictFunctor`
preserves finite limits
(`AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits`), so it carries
`ker δ_m` to the kernel of the restricted `δ_m`, and it preserves epimorphisms, being a left
adjoint.

## Main results

* `Stacks.Coherent.comp_restrictFunctor_map_eq_zero_of_adicBound` — **the pro-zero form of the
  Artin–Rees bound, after restriction to an open of the base**: a morphism into the restriction of
  the `m`-th level of `(π_*𝓕) ^∧` killed by the restricted `δ_m` is killed by the restricted
  transition map down to level `k`.
* `Stacks.Coherent.eq_of_restrictFunctor_comp_directImageQuotientComparison_eq` — **uniqueness of
  the characterized `α` over an open of the base, unconditional and at an arbitrary coherent adic
  system.** Two morphisms of the restricted systems with the same composite with the restriction
  of `δ` are equal.
* `Stacks.Coherent.localAppOpen_eq_of_restrictedCharacterization` — **the overlap agreement of
  Stacks 088B's local solutions is automatic.** This is the binder `hψ` of the two glueings,
  proved.
* `Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions` —
  **Stacks 088B at a general base, from the local solutions over the affine opens alone**: the
  glueing with `hψ` deleted.
* `Stacks.Algebraization.HasAffineLocalDirectImageSolution` and
  `Stacks.Algebraization.isDirectImageComparison_of_hasAffineLocalDirectImageSolution` —
  **`Stacks.Algebraization.IsDirectImageComparison` reduced to the local solution over an affine
  open of the base.** The reduction of the source's first paragraph, with nothing left of it: what
  remains is the source's second paragraph, the flat base change along `B ⟶ B ^∧` over a single
  affine open.
* `Stacks.Algebraization.hDev_of_isDirectImageComparison` — **the binder `hDev` of
  [Stacks, Tag 088E] follows from `Stacks.Algebraization.IsDirectImageComparison`**, with no
  antecedent of its own: on a closed subscheme proper over `A`,
  `Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison` is the whole
  of [Stacks, Tag 088C].
* `Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` —
  **[Stacks, Tag 088E] from two inputs only**: Stacks 088B at a general base, and the Chow
  transport `hTransport` of
  `Stacks.Algebraization.chowComparison_of_isDirectImageComparison`. Both binders of
  `Stacks.Algebraization.isEquivalence_completionFunctorProperOver` are discharged from them.

## What remains

The three binders `ψ`, `hchar`, `hann` of the glueing are the local solutions, i.e. the source's
second paragraph over one affine open of the base. Their ingredients are all available:
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase`
solves the problem over `Spec B ^∧` with no completeness hypothesis on `B`,
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionPullback` descends it
along `B ⟶ B ^∧`, and
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeGamma` assembles the two
at the actual base change with only the square `hγ` outstanding. Three things stand between those
and the binders here, and none of them is addressed in this file: the transport of the situation
over an affine open `V ⊆ X` to one over `Spec Γ(V, 𝒪_X)`; the identification of the restricted `δ`
and `γ_n` with the `δ` and `γ_n` of `π ∣_ V`, which is
`Stacks.Coherent.directImageQuotientComparison_restrict` and
`Stacks.Coherent.directImageComparison_app_restrict_unit` together with the comparison of the two
presentations of the target; and the return of the annihilation along `B ⟶ B ^∧`, which is
`Stacks.Algebraization.exists_primaryComponent_baseChange_equiv_adicCompletion` applied to the
levelwise kernels and cokernels.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, agreeing with it only at
default transparency, so the ambient category of a `kernel`, of a zero morphism or of
`CategoryTheory.Category.assoc` is named explicitly with `(C := _)` or `(obj := _)` rather than
left to unification, as elsewhere in this development.

The overlap agreement is proved at the *sheaf* level over the common open and only then read on
sections, by `Stacks.Algebraization.localAppOpen_eq_of_restrictDown_eq`: a morphism out of a
completion is pinned down by the projections out of it, and
`Stacks.Algebraization.epi_completionProjection` is an epimorphism of sheaves of modules, not a
surjection on the sections over a fixed open, so the comparison cannot be made on sections.

## References

* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

open Stacks.Algebraization Stacks.AdicBoundAffineChart

/-! ### The Artin–Rees bound after restriction to an open of the base -/

section ProZero

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J : X.IdealSheafData)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

/-- **The pro-zero form of the degree-zero Artin–Rees bound, after restriction to an open of the
base.** Let `W ⊆ X` be open, let `k ≤ m` be a pair at which the bound
`Stacks.Coherent.IsDirectImageAdicBounded` holds, and let `d` be a morphism of
`𝒪_W`-modules into the restriction to `W` of the `m`-th level of `(π_*𝓕) ^∧`. If `d` is killed by
the restriction of `δ_m`, it is killed by the restriction of the transition map down to level `k`.

Over `W = X` this is `Stacks.Coherent.kernel_directImageQuotientComparisonApp_comp_map_eq_zero`
with the kernel inclusion replaced by an arbitrary morphism killed by `δ_m`, which is the same
statement. What makes it survive restriction is that
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` preserves finite limits, so it carries
`ker δ_m` to the kernel of the restricted `δ_m` and `d` factors through the restriction of the
kernel inclusion. -/
public theorem comp_restrictFunctor_map_eq_zero_of_adicBound (W : X.Opens) {k m : ℕ}
    (hkm : k ≤ m)
    (har : kernel.ι (C := X.Modules)
        ((Scheme.Modules.pushforward π).map (completionProjection X' (J.comap π) 𝓕 m)) ≫
      completionProjection X J (properPushforwardCoherent π 𝓕) k = 0)
    {Z : W.toScheme.Modules}
    (d : Z ⟶ (Scheme.Modules.restrictFunctor W.ι).obj
      (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.obj (op m)))
    (h : d ≫ (Scheme.Modules.restrictFunctor W.ι).map
      (directImageQuotientComparisonApp π J 𝓕 m) = 0) :
    d ≫ (Scheme.Modules.restrictFunctor W.ι).map
      (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
        (homOfLE hkm).op) = 0 := by
  have hker := kernel_directImageQuotientComparisonApp_comp_map_eq_zero π J 𝓕 hkm har
  have hF : (Scheme.Modules.restrictFunctor W.ι).map
        (kernel.ι (C := X.Modules) (directImageQuotientComparisonApp π J 𝓕 m)) ≫
      (Scheme.Modules.restrictFunctor W.ι).map
        (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
          (homOfLE hkm).op) = 0 :=
    ((Scheme.Modules.restrictFunctor W.ι).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.restrictFunctor W.ι).map hker).trans
        (Functor.map_zero (Scheme.Modules.restrictFunctor W.ι) _ _))
  have hι : kernel.ι (C := W.toScheme.Modules)
        ((Scheme.Modules.restrictFunctor W.ι).map
          (directImageQuotientComparisonApp π J 𝓕 m)) =
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor W.ι)
          (directImageQuotientComparisonApp π J 𝓕 m)).inv ≫
        (Scheme.Modules.restrictFunctor W.ι).map
          (kernel.ι (C := X.Modules) (directImageQuotientComparisonApp π J 𝓕 m)) :=
    (PreservesKernel.iso_inv_ι (Scheme.Modules.restrictFunctor W.ι)
      (directImageQuotientComparisonApp π J 𝓕 m)).symm
  -- the kernel of the restricted `δ_m` is killed by the restricted transition map
  have key : kernel.ι (C := W.toScheme.Modules)
        ((Scheme.Modules.restrictFunctor W.ι).map
          (directImageQuotientComparisonApp π J 𝓕 m)) ≫
      (Scheme.Modules.restrictFunctor W.ι).map
        (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
          (homOfLE hkm).op) = 0 := by
    rw [hι, Category.assoc, hF, comp_zero]
  calc d ≫ (Scheme.Modules.restrictFunctor W.ι).map
            (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
              (homOfLE hkm).op)
      = (kernel.lift (C := W.toScheme.Modules) _ d h ≫
          kernel.ι (C := W.toScheme.Modules)
            ((Scheme.Modules.restrictFunctor W.ι).map
              (directImageQuotientComparisonApp π J 𝓕 m))) ≫
        (Scheme.Modules.restrictFunctor W.ι).map
          (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
            (homOfLE hkm).op) :=
        congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor W.ι).map
            (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
              (homOfLE hkm).op))
          (kernel.lift_ι (C := W.toScheme.Modules) _ d h).symm
    _ = kernel.lift (C := W.toScheme.Modules) _ d h ≫
          (kernel.ι (C := W.toScheme.Modules)
              ((Scheme.Modules.restrictFunctor W.ι).map
                (directImageQuotientComparisonApp π J 𝓕 m)) ≫
            (Scheme.Modules.restrictFunctor W.ι).map
              (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
                (homOfLE hkm).op)) :=
        Category.assoc (obj := W.toScheme.Modules) _ _ _
    _ = 0 := by rw [key, comp_zero]

end ProZero

/-! ### Uniqueness of the characterized `α` over an open of the base -/

section RestrictedUniqueness

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J : X.IdealSheafData)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

/-- **Uniqueness of the characterized `α` over an open of the base, at an arbitrary coherent adic
system, with no hypothesis.** Two morphisms `u`, `v` of the restriction to `W ⊆ X` of `(𝒢_n)`
into the restriction of `(π_*𝓕) ^∧` whose composites with the restriction of `δ` agree are equal.

This is the uniqueness clause of the proof of Stacks 088B in the form the localization of that
proof needs, and unlike
`Stacks.AdicBoundAffineChart.eq_of_comp_directImageQuotientComparisonSystem_eq` it asks nothing of
the source: `(𝒢_n)` is an arbitrary object of `Coh(X, 𝒥)`, not a completion. The argument is the
pro-zero one — `Stacks.Coherent.comp_restrictFunctor_map_eq_zero_of_adicBound` at a pair supplied
by `Stacks.AdicBoundAffineChart.isDirectImageAdicBounded`, against the epimorphy of the transition
maps of a coherent adic system — and it is what makes the overlap hypothesis of the glueing of
Stacks 088B free. -/
public theorem eq_of_restrictFunctor_comp_directImageQuotientComparison_eq (W : X.Opens)
    (G : CoherentAdicSystems J)
    {u v : G.obj ⋙ Scheme.Modules.restrictFunctor W.ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor W.ι}
    (h : ∀ n : ℕ, u.app (op n) ≫ (Scheme.Modules.restrictFunctor W.ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) =
          v.app (op n) ≫ (Scheme.Modules.restrictFunctor W.ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj)) :
    u = v := by
  -- the hypothesis, read with the component of `δ` as a morphism of systems
  have hApp : ∀ n : ℕ, u.app (op n) ≫ (Scheme.Modules.restrictFunctor W.ι).map
        (directImageQuotientComparisonApp π J 𝓕 n) =
      v.app (op n) ≫ (Scheme.Modules.restrictFunctor W.ι).map
        (directImageQuotientComparisonApp π J 𝓕 n) := by
    intro n
    have hsplit : (Scheme.Modules.restrictFunctor W.ι).map
          (directImageQuotientComparisonApp π J 𝓕 n) =
        (Scheme.Modules.restrictFunctor W.ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) ≫
          (Scheme.Modules.restrictFunctor W.ι).map
            (eqToHom (pushforward_completion_obj π J 𝓕 n).symm) := by
      rw [← Functor.map_comp]
      exact congrArg (Scheme.Modules.restrictFunctor W.ι).map
        (Category.assoc (obj := X.Modules) _ _ _).symm
    rw [hsplit, ← Category.assoc, ← Category.assoc, h n]
  refine NatTrans.ext (funext fun n => ?_)
  -- the Artin--Rees pair above the level `n`
  obtain ⟨m, hnm, har⟩ := isDirectImageAdicBounded π J 𝓕 n.unop
  have hd : (u.app (op m) - v.app (op m)) ≫ (Scheme.Modules.restrictFunctor W.ι).map
      (directImageQuotientComparisonApp π J 𝓕 m) = 0 := by
    rw [Preadditive.sub_comp, hApp m, sub_self]
  have hzero := comp_restrictFunctor_map_eq_zero_of_adicBound π J 𝓕 W hnm har
    (u.app (op m) - v.app (op m)) hd
  -- the naturality squares of `u` and of `v` at the transition map
  have hnat : (Scheme.Modules.restrictFunctor W.ι).map (G.obj.map (homOfLE hnm).op) ≫
      (u.app (op n.unop) - v.app (op n.unop)) = 0 := by
    have hu := u.naturality (homOfLE hnm).op
    have hv := v.naturality (homOfLE hnm).op
    rw [Preadditive.comp_sub]
    rw [show (Scheme.Modules.restrictFunctor W.ι).map (G.obj.map (homOfLE hnm).op) ≫
          u.app (op n.unop) =
        u.app (op m) ≫ (Scheme.Modules.restrictFunctor W.ι).map
          (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
            (homOfLE hnm).op) from hu,
      show (Scheme.Modules.restrictFunctor W.ι).map (G.obj.map (homOfLE hnm).op) ≫
          v.app (op n.unop) =
        v.app (op m) ≫ (Scheme.Modules.restrictFunctor W.ι).map
          (((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj.map
            (homOfLE hnm).op) from hv,
      ← Preadditive.sub_comp]
    exact hzero
  -- and the transition map of a coherent adic system is an epimorphism
  have hepi : Epi ((Scheme.Modules.restrictFunctor W.ι).map
      (G.obj.map (homOfLE hnm).op)) :=
    have : Epi (G.obj.map (homOfLE hnm).op) := G.property.epi_map hnm
    (Scheme.Modules.restrictFunctor W.ι).map_epi _
  have := (@cancel_epi _ _ _ _ _ ((Scheme.Modules.restrictFunctor W.ι).map
    (G.obj.map (homOfLE hnm).op)) hepi _ _).mp
      (hnat.trans (comp_zero (C := W.toScheme.Modules)).symm)
  exact sub_eq_zero.mp this

end RestrictedUniqueness

/-! ### The overlap agreement of the local solutions of Stacks 088B -/

section Overlap

/-- **The comparison of the two routes down to a smaller open is natural in the module, read on
the inverses.** This is `Stacks.Algebraization.restrictDownIso_hom_naturality` conjugated. -/
private theorem restrictDownIso_inv_naturality {Y : Scheme.{u}} {U W : Y.Opens} (hWU : W ≤ U)
    {M N : Y.Modules} (φ : M ⟶ N) :
    (restrictDownIso hWU M).inv ≫ (Scheme.Modules.restrictFunctor W.ι).map φ =
      (Scheme.Modules.restrictFunctor (Y.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctor U.ι).map φ) ≫
        (restrictDownIso hWU N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← restrictDownIso_hom_naturality hWU φ, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The restriction to a smaller open of a morphism of two inverse systems restricted to an
open.** Levelwise it is the conjugate of the given morphism by
`Stacks.Algebraization.restrictDownIso`; the naturality is the naturality of that comparison
(`Stacks.Algebraization.restrictDownIso_hom_naturality` and its inverse form) together with the
naturality of the given morphism.

This is the morphism-level analogue of
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.restrictIsoOfLE`, which the library has only for
isomorphisms; it is private because its only purpose is to compare two local solutions of
Stacks 088B over a common open, which is
`Stacks.Coherent.localAppOpen_eq_of_restrictedCharacterization`. -/
private def restrictSystemHomOfLE {Y : Scheme.{u}} {U W : Y.Opens} (hWU : W ≤ U)
    {Cc : Type*} [Category Cc] {A B : Cc ⥤ Y.Modules}
    (ψ : A ⋙ Scheme.Modules.restrictFunctor U.ι ⟶ B ⋙ Scheme.Modules.restrictFunctor U.ι) :
    A ⋙ Scheme.Modules.restrictFunctor W.ι ⟶ B ⋙ Scheme.Modules.restrictFunctor W.ι where
  app k := (restrictDownIso hWU (A.obj k)).hom ≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE hWU)).map (ψ.app k) ≫
      (restrictDownIso hWU (B.obj k)).inv
  naturality k l g := by
    have hψ := ψ.naturality g
    simp only [Functor.comp_map] at hψ
    simp only [Functor.comp_map, Category.assoc]
    rw [← Category.assoc, restrictDownIso_hom_naturality hWU (A.map g)]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hψ, Functor.map_comp_assoc,
      ← restrictDownIso_inv_naturality hWU (B.map g)]

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

/-- **The restriction of a local solution to a smaller open is a local solution there.** For
`W ≤ U` and a morphism `ψ` of the systems restricted to `U` satisfying the restricted
characterization of Stacks 088B over `U`, the conjugate of `ψ` by
`Stacks.Algebraization.restrictDownIso` — the comparison of the two routes from `X` down to `W` —
satisfies the restricted characterization over `W`.

Both steps are the naturality of `Stacks.Algebraization.restrictDownIso`
(`Stacks.Algebraization.restrictDownIso_hom_naturality`), at the restricted `δ_n` and at the
restricted `γ_n`: it carries the two sides of the equation over `U` to the two sides of the
equation over `W`. No property of `ψ` beyond the equation is used. -/
public theorem restrictDown_comp_directImageQuotientComparison
    (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)
    {U W : X.Opens} (hWU : W ≤ U)
    (ψ : G.obj ⋙ Scheme.Modules.restrictFunctor U.ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor U.ι)
    (hchar : ∀ n : ℕ, (ψ).app (op n) ≫
          (Scheme.Modules.restrictFunctor U.ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) =
        (Scheme.Modules.restrictFunctor U.ι).map
          ((directImageComparison π J G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj π J 𝓕 n)))
    (n : ℕ) :
    ((restrictDownIso hWU (G.obj.obj (op n))).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map (ψ.app (op n)) ≫
          (restrictDownIso hWU
            (((completionFunctor X J).obj
              (properPushforwardCoherent π 𝓕)).obj.obj (op n))).inv) ≫
        (Scheme.Modules.restrictFunctor W.ι).map
          (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
            directImageQuotientComparison π J (n + 1) 𝓕.obj) =
      (Scheme.Modules.restrictFunctor W.ι).map
        ((directImageComparison π J G 𝓕 β).app (op n) ≫
          eqToHom (pushforward_completion_obj π J 𝓕 n)) := by
  simp only [Category.assoc]
  rw [restrictDownIso_inv_naturality hWU
      (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
        directImageQuotientComparison π J (n + 1) 𝓕.obj),
    ← Functor.map_comp_assoc, hchar n, ← Category.assoc,
    ← restrictDownIso_hom_naturality hWU
      ((directImageComparison π J G 𝓕 β).app (op n) ≫
        eqToHom (pushforward_completion_obj π J 𝓕 n)),
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The overlap agreement of the local solutions of Stacks 088B is automatic.** Two morphisms
`ψ`, `ψ'` of the systems restricted to two opens `U`, `U'` of the base, each satisfying the
restricted characterization of Stacks 088B over its own open, act in the same way on the sections
over every open `V` contained in both.

This is verbatim the binder `hψ` of
`Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover` and of
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover`, and it is
the content of the source's "`α` is unique, so we may work locally". It is **unconditional**: the
systems are arbitrary and nothing is assumed algebraizable.

The comparison is made at the sheaf level over `V` and only then read on sections, by
`Stacks.Algebraization.localAppOpen_eq_of_restrictDown_eq`. The two restrictions down to `V` are
local solutions there, by
`Stacks.Coherent.restrictDown_comp_directImageQuotientComparison`, and they agree by
`Stacks.Coherent.eq_of_restrictFunctor_comp_directImageQuotientComparison_eq`. -/
public theorem localAppOpen_eq_of_restrictedCharacterization
    (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)
    {U U' : X.Opens}
    (ψ : G.obj ⋙ Scheme.Modules.restrictFunctor U.ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor U.ι)
    (ψ' : G.obj ⋙ Scheme.Modules.restrictFunctor U'.ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor U'.ι)
    (hchar : ∀ n : ℕ, ψ.app (op n) ≫
          (Scheme.Modules.restrictFunctor U.ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) =
        (Scheme.Modules.restrictFunctor U.ι).map
          ((directImageComparison π J G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj π J 𝓕 n)))
    (hchar' : ∀ n : ℕ, ψ'.app (op n) ≫
          (Scheme.Modules.restrictFunctor U'.ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) =
        (Scheme.Modules.restrictFunctor U'.ι).map
          ((directImageComparison π J G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj π J 𝓕 n)))
    (n : ℕᵒᵖ) {V : X.Opens} (hVU : V ≤ U) (hVU' : V ≤ U') :
    localAppOpen U (ψ.app n) hVU = localAppOpen U' (ψ'.app n) hVU' := by
  refine localAppOpen_eq_of_restrictDown_eq hVU hVU' (ψ.app n) (ψ'.app n) ?_
  -- the two restrictions down to `V` are local solutions there, hence equal
  have hχ : restrictSystemHomOfLE hVU ψ = restrictSystemHomOfLE hVU' ψ' :=
    eq_of_restrictFunctor_comp_directImageQuotientComparison_eq π J 𝓕 V G fun k =>
      (restrictDown_comp_directImageQuotientComparison π J G 𝓕 β hVU ψ hchar k).trans
        (restrictDown_comp_directImageQuotientComparison π J G 𝓕 β hVU' ψ' hchar' k).symm
  exact congrArg (fun z => NatTrans.app z n) hχ

end Overlap

/-! ### Stacks 088B at a general base, from the local solutions alone -/

section Assembly

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)

/-- **Both halves of the conclusion of Stacks 088B at a general base, from the local solutions
over the affine opens of the base alone.** Let `π : X' ⟶ X` be proper with `X'`, `X` Noetherian,
let `𝒥, 𝒦 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals, let `(𝒢_n)` be an object of
`Coh(X, 𝒥)`, let `𝓕` be a coherent `𝒪_{X'}`-module and `β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Given, over each
affine open `V` of `X`, a morphism `ψ V` of the restricted systems which

* satisfies the restricted characterization `hchar`, and
* has its levelwise kernels and cokernels annihilated by a power of `𝒦|_V`, `hann`,

there is a morphism `α : (𝒢_n) ⟶ (π_*𝓕) ^∧` restricting to each `ψ V` which is characterized in
the sense of `Stacks.Coherent.IsDirectImageCharacterized` **and** has its levelwise kernels and
cokernels annihilated by a power of `𝒦`.

This is `Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover`
with its overlap binder `hψ` **deleted**, discharged by
`Stacks.Coherent.localAppOpen_eq_of_restrictedCharacterization`: two local solutions over two
opens of the base agree on the sections over any open contained in both, with no hypothesis.
What is left are the local solutions themselves, which are the source's second paragraph over one
affine open; see the module docstring for where each of their ingredients stands. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions
    (ψ : ∀ V : X.affineOpens, G.obj ⋙ Scheme.Modules.restrictFunctor V.1.ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor V.1.ι)
    (hchar : ∀ (V : X.affineOpens) (n : ℕ), (ψ V).app (op n) ≫
          (Scheme.Modules.restrictFunctor V.1.ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) =
        (Scheme.Modules.restrictFunctor V.1.ι).map
          ((directImageComparison π J G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj π J 𝓕 n)))
    (hann : ∀ V : X.affineOpens,
      IsKernelCokernelAnnihilatedByPower (K.comap V.1.ι) (ψ V)) :
    ∃ α : G.obj ⟶ ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π J G 𝓕 β α ∧
        IsKernelCokernelAnnihilatedByPower K α ∧
          ∀ V : X.affineOpens,
            Functor.whiskerRight α (Scheme.Modules.restrictFunctor V.1.ι) = ψ V :=
  exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover π J K G 𝓕 β ψ
    (fun V W n _ hOV hOW => localAppOpen_eq_of_restrictedCharacterization π J G 𝓕 β
      (ψ V) (ψ W) (hchar V) (hchar W) n hOV hOW)
    hchar hann

end Assembly

end Stacks.Coherent

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### `IsDirectImageComparison` reduced to the local solution over an affine open -/

/-- **The local solution of Stacks 088B over an affine open of the base.** For every proper
morphism `π : X' ⟶ X` of Noetherian schemes, every pair `𝒥, 𝒦` of quasi-coherent ideal sheaves on
`X`, every coherent `𝒪_{X'}`-module `𝓕`, every object `(𝒢_n)` of `Coh(X, 𝒥)`, every
`β : π^*(𝒢_n) ≅ 𝓕 ^∧` and every affine open `V ⊆ X`: granted the source's hypothesis that `π` is
an isomorphism over `X ∖ V(𝒦)`, there is a morphism of the systems restricted to `V` which
satisfies the restricted characterization of Stacks 088B and has its levelwise kernels and
cokernels annihilated by a power of `𝒦|_V`.

This is the whole of what the localization of the proof of Stacks 088B asks of its local data —
the binders `ψ`, `hchar` and `hann` of
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions`,
packaged as a single statement so that it can be carried as one hypothesis. It is the source's
second paragraph: over the affine `V = Spec B` the ring `B` need not be complete along `𝒥(V)`, so
Grothendieck existence is unavailable there, and the source replaces `B` by `B ^∧`, solves the
problem over `Spec B ^∧` and transports the conclusion back.

No `stacks` attribute is attached: this is a hypothesis, not a statement of the source. -/
public def HasAffineLocalDirectImageSolution : Prop :=
  ∀ {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
    (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕),
    IsIso (π ∣_ K.support.compl) →
      ∀ V : X.affineOpens,
        ∃ ψ : G.obj ⋙ Scheme.Modules.restrictFunctor V.1.ι ⟶
          ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
            Scheme.Modules.restrictFunctor V.1.ι,
          (∀ n : ℕ, ψ.app (op n) ≫
                (Scheme.Modules.restrictFunctor V.1.ι).map
                  (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
                    directImageQuotientComparison π J (n + 1) 𝓕.obj) =
              (Scheme.Modules.restrictFunctor V.1.ι).map
                ((directImageComparison π J G 𝓕 β).app (op n) ≫
                  eqToHom (pushforward_completion_obj π J 𝓕 n))) ∧
            IsKernelCokernelAnnihilatedByPower (K.comap V.1.ι) ψ

/-- **[Stacks, Tag 088B] at a general base, reduced to the local solution over an affine open of
the base.** `Stacks.Algebraization.IsDirectImageComparison` — the form of Stacks 088B that
[Stacks, Tag 088C], `hDev` and `hSupp` consume, at an arbitrary Noetherian base and an arbitrary
quasi-coherent ideal sheaf, with no morphism to an affine base anywhere — follows from
`Stacks.Algebraization.HasAffineLocalDirectImageSolution`.

Everything between the two is proved: the glueing of the characterization is
`Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover`, the glueing of the annihilation
is `Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover`, and
the overlap agreement of the local solutions, which both of those carry as a binder, is
`Stacks.Coherent.localAppOpen_eq_of_restrictedCharacterization`. So the source's first paragraph
is discharged in full, and what is left of Stacks 088B at a general base is its second paragraph
over a single affine open.

No `stacks` attribute is attached: the tag is registered on
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions`,
which is this statement with the data spelled out instead of existentially quantified. -/
public theorem isDirectImageComparison_of_hasAffineLocalDirectImageSolution
    (h : HasAffineLocalDirectImageSolution.{u}) : IsDirectImageComparison.{u} := by
  intro X' X _ _ π _ J K 𝓕 G β hiso
  choose ψ hchar hann using h π J K G 𝓕 β hiso
  obtain ⟨α, -, hann', -⟩ :=
    exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions π J K G 𝓕 β ψ
      hchar hann
  exact ⟨α, hann'⟩

/-! ### The binder `hDev` of Stacks 088E, from Stacks 088B at a general base -/

/-- **The hypothesis `hDev` of [Stacks, Tag 088E], from [Stacks, Tag 088B] at a general base.**
The inductive step of the Noetherian induction of Stacks 088C, asked on every closed subscheme of
`X` proper over `A` — which is where the source applies 088C — holds as soon as
`Stacks.Algebraization.IsDirectImageComparison` does.

It carries no antecedent of its own: on a closed subscheme `K` with `K.subscheme ⟶ Spec A`
proper, `Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison` is the
whole of Stacks 088C there, so *every* coherent adic system is in the essential image of the
completion functor and the dévissage hypothesis `hInd` is not used. This is verbatim the binder
`hDev` of `Stacks.Algebraization.isEquivalence_completionFunctorProperOver`.

No `stacks` attribute is attached: Stacks 088C is registered on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`, and this is that theorem's
conclusion read on the closed subschemes. -/
public theorem hDev_of_isDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (h088B : IsDirectImageComparison.{u}) :
    ∀ (K : X.IdealSheafData) (hK : IsProper (K.subschemeι ≫ f)),
      letI : IsProper (K.subschemeι ≫ f) := hK
      letI : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
      ∀ L : K.subscheme.IdealSheafData,
        (∀ L' : K.subscheme.IdealSheafData, L < L' →
            ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
                (baseIdealSheaf A I (K.subschemeι ≫ f)),
              IsSystemAnnihilatedBy L' 𝓖.obj →
                (completionFunctor K.subscheme
                  (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓖) →
          ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems
              (baseIdealSheaf A I (K.subschemeι ≫ f)),
            IsSystemAnnihilatedBy L 𝓕.obj →
              (completionFunctor K.subscheme
                (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓕 := by
  intro K hK
  let : IsProper (K.subschemeι ≫ f) := hK
  let : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  have :=
    isEquivalence_completionFunctor_of_isDirectImageComparison A I h088B (K.subschemeι ≫ f)
  exact fun _ _ 𝓕 _ => Functor.EssSurj.mem_essImage _ 𝓕

/-! ### Stacks 088E from Stacks 088B at a general base and the Chow transport -/

/-- **[Stacks, Tag 088E], Grothendieck's existence theorem, from [Stacks, Tag 088B] at a general
base and the transport of a coherent adic system to a projective compactification.** For `A`
Noetherian and complete along `I` and `f : X ⟶ Spec A` separated, locally of finite type and
quasi-compact, the functor of Stacks 088D is an equivalence, granted

* `h088B`, `Stacks.Algebraization.IsDirectImageComparison`, and
* `hTransport`, the Chow datum of the second half of the source's proof, in the repaired
  disjunctive form of `Stacks.Algebraization.chowComparison_of_isDirectImageComparison`.

Both binders of `Stacks.Algebraization.isEquivalence_completionFunctorProperOver` are discharged
from these two: `hDev` by `Stacks.Algebraization.hDev_of_isDirectImageComparison`, and `hSupp` by
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` read through
`Stacks.Algebraization.hSupp_of_isProper_systemAnnihilatorIdeal`.

No `stacks` attribute is attached: Stacks 088E is registered on
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver`, and this is that statement with
its two binders replaced by the two inputs above. -/
public theorem isEquivalence_completionFunctorProperOver_of_isDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u})
    (hTransport : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      letI : IsNoetherian X := { }
      ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
            ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (_ : IsProper π) (_ : IsNoetherian Y) (U : X.Opens),
              IsIso (π ∣_ U) ∧
                (∀ e : ℕ, K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
                    (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)) ^ (e + 1)) ∧
                  ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
                    HasProperSupport (π ≫ f) G.obj ∧
                      Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                        (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj G)) :
    (completionFunctorProperOver A I f).IsEquivalence :=
  isEquivalence_completionFunctorProperOver A I f (hDev_of_isDirectImageComparison A I f h088B)
    (hSupp_of_isProper_systemAnnihilatorIdeal A I f
      (isProper_systemAnnihilatorIdeal_of_transport A I f h088B hTransport))

end Stacks.Algebraization

end
