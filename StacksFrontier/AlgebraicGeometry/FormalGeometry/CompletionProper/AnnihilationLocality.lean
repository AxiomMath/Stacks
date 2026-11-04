module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GeneralBaseAlgebraization
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# The annihilation half of the conclusion of Stacks 088B is local on the base

Stacks 088B produces, from an object `(𝒢_n)` of `Coh(X, 𝒥)` and the data `𝓕`, `β` of its proof, a
morphism of inverse systems

`α : (𝒢_n) ⟶ (π_*𝓕) ^∧`

with two properties: it is *characterized* by its composites with
`Stacks.Coherent.directImageComparison`, and its levelwise kernels and cokernels are *annihilated
by a power of `𝒦`*. `CompletionProper/GeneralBaseAlgebraization.lean` glues the first property
over an arbitrary open cover of the base —
`Stacks.Coherent.isDirectImageCharacterized_iff_restrictCover` is an unconditional iff — and
records that the second is not glued there, because
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` asks for *one* exponent `t` valid at
every level `k` at once. Transporting such a condition from the members of a cover needs three
things, and this file supplies them and assembles them.

1. **Locality of vanishing.** For a *fixed* exponent `n`, the condition `𝒦 ⁿ M = ⊥` is local on
   the base. Both halves are already in the library —
   `Stacks.Algebraization.idealPowerMultiple_restrict_eq_bot` restricts it and
   `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict` glues it — and
   `Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_restrictCover` is the iff they make,
   which is the form the exponent bookkeeping below consumes. The gluing direction is where the
   sheaf condition is used: an affine open of `X` need not be contained in a member of the cover,
   so the vanishing of a product `r • x` is checked on the affine opens that are and then
   promoted.

2. **Exactness of restriction on the levelwise kernels and cokernels.** What is needed is not that
   restriction to an open is exact but that it *commutes with forming those kernels and
   cokernels*: the levelwise kernel of the restricted `α` is the restriction of the levelwise
   kernel of `α`, and likewise for cokernels. As annihilation statements this is
   `Stacks.Algebraization.idealPowerMultiple_kernel_restrictFunctor_map_eq_bot_iff` and
   `Stacks.Algebraization.idealPowerMultiple_cokernel_restrictFunctor_map_eq_bot_iff`, the
   comparison isomorphisms being `CategoryTheory.Limits.PreservesKernel.iso` and
   `CategoryTheory.Limits.PreservesCokernel.iso` for
   `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which preserves finite limits (it is
   isomorphic to pullback along a flat morphism) and all colimits (it is a left adjoint).

3. **Uniformity of the exponent over a finite cover.** With 1 and 2 in hand, each member `j` of
   the cover supplies an exponent `t j` uniform in the level, and the maximum of finitely many
   such exponents is one exponent uniform in the level *and* in the member. This is the step that
   needs finiteness, and it is the reason the per-level exponents of
   `AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset` (Tag 01Y9) are not enough
   on their own: that result bounds nothing uniformly in the level, so an infinite family of
   exponents with no bound gives no `t`.

Finiteness is *obtained* rather than assumed wherever the base is quasi-compact: the affine opens
of a scheme form a basis of its topology, so a quasi-compact base is covered by finitely many of
them, and `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_affineOpens` takes the
hypothesis over *every* affine open with no finiteness binder at all. The base of Stacks 088B is
Noetherian, hence quasi-compact, so the capstone over an affine open cover carries no finiteness
hypothesis either.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_restrictCover` — **piece 1**: for a fixed
  exponent, `𝒦 ⁿ M = ⊥` holds exactly when it holds after restricting to each member of an open
  cover. Unconditional, any index type, no quasi-coherence of `M`.
* `Stacks.Algebraization.idealPowerMultiple_kernel_restrictFunctor_map_eq_bot_iff` and
  `Stacks.Algebraization.idealPowerMultiple_cokernel_restrictFunctor_map_eq_bot_iff` — **piece
  2**: restriction to an open commutes with forming the kernel and the cokernel of a morphism, so
  far as annihilation by a power of an ideal sheaf can see.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_restrictCover` — **piece 3**, and
  the general theorem: over a *finite* open cover of the base, levelwise kernels and cokernels
  annihilated by a power of `𝒦|_{U j}` after restriction to each member are annihilated by a
  power of `𝒦` globally.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_affineOpens` — the same with the
  finiteness binder discharged by quasi-compactness of the base, the hypothesis being taken over
  every affine open.
* `Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_finite_openCover` and
  `Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover` — **the
  deliverable**: the `α` glued from an open cover of the base by
  `Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover` satisfies *both* halves of the
  conclusion of Stacks 088B, the annihilation half as well as the characterization, as soon as
  the local solutions satisfy the annihilation half over their members. Over an affine open cover
  there is no finiteness hypothesis.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, agreeing with it only at
default transparency, so instance search does not see through it; the complete lattice of
submodules is supplied by the local instance
`AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice`, as elsewhere in this development, and
the ambient category of a `kernel` or `cokernel` is named explicitly with `(C := _)` rather than
left to unification.

The levelwise restricted morphism is `CategoryTheory.Functor.whiskerRight α (restrictFunctor _)`,
whose component at `op k` *is* `(restrictFunctor _).map (α.app (op k))`; piece 2 is therefore
stated for a bare morphism of sheaves of modules and applied to those components directly.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u v

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Piece 1: vanishing of `𝒦 ⁿ M` is local on the base -/

/-- **Annihilation by a fixed power of an ideal sheaf is local on the base, as an iff.** For one
fixed exponent `n`, the subsheaf `ℐ ⁿ M` is zero exactly when its restriction to each member of
an open cover of `X` is zero.

Both directions are already theorems: `Stacks.Algebraization.idealPowerMultiple_restrict_eq_bot`
restricts the vanishing along an open immersion, and
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict` glues it back. This is the iff they
make, which is the form in which the exponent bookkeeping of
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_restrictCover` uses them.

Unconditional: the index type of the cover is arbitrary, its members need not be affine or
quasi-compact, and `M` need not be quasi-coherent. The exponent is fixed throughout — it is only
the passage from a fixed exponent to the *existence* of one that costs quasi-compactness, since
the local data then supply one exponent per member. -/
public theorem idealPowerMultiple_eq_bot_iff_restrictCover {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) {J : Type v} (U : J → X.Opens)
    (hU : IsOpenCover U) :
    idealPowerMultiple I n M = ⊥ ↔
      ∀ j, idealPowerMultiple (I.comap (U j).ι) n
        ((Scheme.Modules.restrictFunctor (U j).ι).obj M) = ⊥ :=
  ⟨fun h j => idealPowerMultiple_restrict_eq_bot (U j).ι I n M h,
    idealPowerMultiple_eq_bot_of_restrict I n M U hU.iSup_eq_top⟩

/-! ### Piece 2: restriction commutes with the kernel and the cokernel -/

/-- Annihilation by `ℒ ⁿ` is invariant under isomorphism. -/
private theorem idealPowerMultiple_eq_bot_iff_of_iso {Y : Scheme.{u}} (L : Y.IdealSheafData)
    (n : ℕ) {M N : Y.Modules} (e : M ≅ N) :
    idealPowerMultiple L n N = ⊥ ↔ idealPowerMultiple L n M = ⊥ :=
  ⟨idealPowerMultiple_eq_bot_of_iso L e n, idealPowerMultiple_eq_bot_of_iso L e.symm n⟩

/-- **Restriction to an open commutes with forming a kernel**, as far as annihilation by a power
of an ideal sheaf can see: the kernel of the restricted morphism is annihilated by `ℒ ⁿ` exactly
when the restriction of the kernel is.

`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along an open immersion preserves finite
limits, being isomorphic to pullback along a flat morphism, so
`CategoryTheory.Limits.PreservesKernel.iso` is an isomorphism between the two sheaves and
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso` transports the vanishing across it in
both directions.

This is the half of the exactness of restriction that the gluing of
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` actually needs: not that restriction
is exact, but that it *commutes* with forming the object whose annihilation is being asserted. -/
public theorem idealPowerMultiple_kernel_restrictFunctor_map_eq_bot_iff {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (L : Y.IdealSheafData) (n : ℕ) {M N : X.Modules}
    (g : M ⟶ N) :
    idealPowerMultiple L n
        (kernel (C := Y.Modules) ((Scheme.Modules.restrictFunctor f).map g)) = ⊥ ↔
      idealPowerMultiple L n
        ((Scheme.Modules.restrictFunctor f).obj (kernel (C := X.Modules) g)) = ⊥ := by
  have hfl : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
    AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor f
  have hpl : PreservesLimitsOfShape WalkingParallelPair (Scheme.Modules.restrictFunctor f) :=
    hfl.preservesFiniteLimits _
  exact idealPowerMultiple_eq_bot_iff_of_iso L n (PreservesKernel.iso _ g)

/-- **Restriction to an open commutes with forming a cokernel**, as far as annihilation by a
power of an ideal sheaf can see.

`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a left adjoint, so it preserves all
colimits and `CategoryTheory.Limits.PreservesCokernel.iso` is an isomorphism;
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso` transports the vanishing across it in
both directions. The cokernel companion of
`Stacks.Algebraization.idealPowerMultiple_kernel_restrictFunctor_map_eq_bot_iff`. -/
public theorem idealPowerMultiple_cokernel_restrictFunctor_map_eq_bot_iff {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (L : Y.IdealSheafData) (n : ℕ) {M N : X.Modules}
    (g : M ⟶ N) :
    idealPowerMultiple L n
        (cokernel (C := Y.Modules) ((Scheme.Modules.restrictFunctor f).map g)) = ⊥ ↔
      idealPowerMultiple L n
        ((Scheme.Modules.restrictFunctor f).obj (cokernel (C := X.Modules) g)) = ⊥ := by
  have hpc : PreservesColimitsOfShape WalkingParallelPair
    (Scheme.Modules.restrictFunctor f) := inferInstance
  exact idealPowerMultiple_eq_bot_iff_of_iso L n (PreservesCokernel.iso _ g)

/-! ### Piece 3: one exponent uniform in the level and in the member of a finite cover -/

/-- **Tag 0888 (1) is local on the base over a finite cover.** Let `α : F ⟶ G` be a morphism of
inverse systems of sheaves of modules on `X` and let `U` be a **finite** open cover of `X`. If
for each member `j` the levelwise kernels and cokernels of the restricted morphism
`α|_{U j}` are annihilated by a power of `𝒦|_{U j}`, then those of `α` are annihilated by a
power of `𝒦`.

This is the three pieces assembled. Member `j` supplies an exponent `t j` which is uniform in the
level `k` but says nothing about the other members; `N` is a bound for the finitely many `t j`,
and `N + 1` is then positive and annihilates every levelwise kernel and cokernel over every
member, by `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le`. Piece 2 identifies the
levelwise kernel and cokernel of the restricted morphism with the restrictions of those of `α`,
and piece 1 glues their vanishing to `X`.

**Finiteness is essential and is not bookkeeping.**
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` demands one exponent for all levels
at once; the per-member exponents come with no a priori
bound — the exponents of `AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset`
(Tag 01Y9) depend on the level — so over an infinite cover their supremum need not exist and no
uniform `t` is available. See
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_affineOpens` for the form in which
the finiteness is produced by quasi-compactness of the base rather than assumed. -/
public theorem isKernelCokernelAnnihilatedByPower_of_restrictCover {X : Scheme.{u}}
    (K : X.IdealSheafData) {F G : ℕᵒᵖ ⥤ X.Modules} (α : F ⟶ G)
    {J : Type v} [Finite J] (U : J → X.Opens) (hU : IsOpenCover U)
    (h : ∀ j, IsKernelCokernelAnnihilatedByPower (K.comap (U j).ι)
      (Functor.whiskerRight α (Scheme.Modules.restrictFunctor (U j).ι))) :
    IsKernelCokernelAnnihilatedByPower K α := by
  obtain ⟨N, hN⟩ := Finite.exists_le fun j => (h j).choose
  refine ⟨N + 1, N.succ_pos, fun k => ⟨?_, ?_⟩⟩
  · refine (idealPowerMultiple_eq_bot_iff_restrictCover K (N + 1)
      (kernel (C := X.Modules) (α.app (op k))) U hU).2 fun j => ?_
    refine (idealPowerMultiple_kernel_restrictFunctor_map_eq_bot_iff (U j).ι
      (K.comap (U j).ι) (N + 1) (α.app (op k))).1 ?_
    exact idealPowerMultiple_eq_bot_of_le ((h j).choose_spec.2 k).1
      ((hN j).trans (Nat.le_succ N))
  · refine (idealPowerMultiple_eq_bot_iff_restrictCover K (N + 1)
      (cokernel (C := X.Modules) (α.app (op k))) U hU).2 fun j => ?_
    refine (idealPowerMultiple_cokernel_restrictFunctor_map_eq_bot_iff (U j).ι
      (K.comap (U j).ι) (N + 1) (α.app (op k))).1 ?_
    exact idealPowerMultiple_eq_bot_of_le ((h j).choose_spec.2 k).2
      ((hN j).trans (Nat.le_succ N))

/-- **Tag 0888 (1) is local on the base, with the finiteness produced rather than assumed.** On a
quasi-compact scheme, levelwise kernels and cokernels annihilated by a power of `𝒦|_V` after
restriction to *every* affine open `V` are annihilated by a power of `𝒦`.

The affine opens of a scheme form a basis of its topology, so quasi-compactness of `X` extracts
from them a finite subfamily covering `X`, and
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_restrictCover` applies to that
finite cover. There is no finiteness hypothesis to discharge at the call site, which is why this
is the form the base of Stacks 088B — Noetherian, hence quasi-compact — can use. It is the
kernel-cokernel analogue of `Stacks.Algebraization.isPowerAnnihilated_of_restrict`, from which it
differs in that each affine open already supplies an exponent uniform in the level. -/
public theorem isKernelCokernelAnnihilatedByPower_of_affineOpens {X : Scheme.{u}}
    [CompactSpace X] (K : X.IdealSheafData) {F G : ℕᵒᵖ ⥤ X.Modules} (α : F ⟶ G)
    (h : ∀ V : X.affineOpens, IsKernelCokernelAnnihilatedByPower (K.comap V.1.ι)
      (Functor.whiskerRight α (Scheme.Modules.restrictFunctor V.1.ι))) :
    IsKernelCokernelAnnihilatedByPower K α := by
  have hbasis : TopologicalSpace.Opens.IsBasis (Set.range fun A : X.affineOpens => A.1) := by
    have heq : Set.range (fun A : X.affineOpens => A.1) = X.affineOpens := by
      ext W
      exact ⟨fun ⟨A, hA⟩ => hA ▸ A.property, fun hW => ⟨⟨W, hW⟩, rfl⟩⟩
    rw [heq]
    exact X.isBasis_affineOpens
  obtain ⟨κ, hκ, a, heq⟩ := hbasis.exists_iSup_eq_of_isCompact (⊤ : X.Opens) isCompact_univ
  exact isKernelCokernelAnnihilatedByPower_of_restrictCover K α (fun k : κ => (a k).1)
    (IsOpenCover.mk heq.symm) fun k => h (a k)

end Stacks.Algebraization

namespace Stacks.Coherent

open Stacks.Algebraization

/-! ### Both halves of the conclusion of Stacks 088B, glued from a cover of the base -/

section Locality

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)

/-- **Both halves of the conclusion of Stacks 088B, glued from a finite open cover of the base.**
Let `π : X' ⟶ X` be proper with `X'`, `X` Noetherian, let `𝒥, 𝒦 ⊆ 𝒪_X` be quasi-coherent sheaves
of ideals, let `(𝒢_n)` be an object of `Coh(X, 𝒥)`, let `𝓕` be a coherent `𝒪_{X'}`-module and
`β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Given a **finite** open cover `U` of `X` and, over each member, a
morphism `ψ j` of the restricted systems which

* satisfies the restricted characterization `hchar`,
* agrees with the others on overlaps, `hψ`, and
* has its levelwise kernels and cokernels annihilated by a power of `𝒦|_{U j}`, `hann`,

there is a morphism `α : (𝒢_n) ⟶ (π_*𝓕) ^∧` restricting to each `ψ j` which is characterized in
the sense of `Stacks.Coherent.IsDirectImageCharacterized` **and** has its levelwise kernels and
cokernels annihilated by a power of `𝒦`.

`Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover` glues the characterization over
an arbitrary cover; what is added here is the annihilation, by
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_restrictCover` applied to the glued
`α`, which restricts to `ψ j` on the nose. Finiteness of the cover enters only there, and only
because the exponent must be uniform in the level. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_finite_openCover
    {Jx : Type u} [Finite Jx] (U : Jx → X.Opens) (hU : IsOpenCover U)
    (ψ : ∀ j, G.obj ⋙ Scheme.Modules.restrictFunctor (U j).ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor (U j).ι)
    (hψ : ∀ (i j : Jx) (n : ℕᵒᵖ) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      localAppOpen (U i) ((ψ i).app n) hVi = localAppOpen (U j) ((ψ j).app n) hVj)
    (hchar : ∀ (j : Jx) (n : ℕ), (ψ j).app (op n) ≫
          (Scheme.Modules.restrictFunctor (U j).ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) =
        (Scheme.Modules.restrictFunctor (U j).ι).map
          ((directImageComparison π J G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj π J 𝓕 n)))
    (hann : ∀ j, IsKernelCokernelAnnihilatedByPower (K.comap (U j).ι) (ψ j)) :
    ∃ α : G.obj ⟶ ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π J G 𝓕 β α ∧
        IsKernelCokernelAnnihilatedByPower K α ∧
          ∀ j, Functor.whiskerRight α (Scheme.Modules.restrictFunctor (U j).ι) = ψ j := by
  obtain ⟨α, hα, hres⟩ :=
    exists_isDirectImageCharacterized_of_openCover π J G 𝓕 β U hU ψ hψ hchar
  refine ⟨α, hα, ?_, hres⟩
  refine isKernelCokernelAnnihilatedByPower_of_restrictCover K α U hU fun j => ?_
  exact (hres j).symm ▸ hann j

/-- **Both halves of the conclusion of Stacks 088B, glued from the affine open cover of the
base, with no finiteness hypothesis.** The cover is the family of *all* affine opens of `X`, and
the finiteness that the uniform exponent needs is produced by the quasi-compactness of `X`, which
`IsNoetherian X` supplies.

This is the shape of the localization step that the proof of Stacks 088B actually wants: the
source reduces to an affine base, and over an affine open of the base the local solution is what
its second paragraph constructs by flat base change along `B ⟶ B ^∧`. The binders `ψ`, `hψ`,
`hchar`, `hann` are exactly those local solutions together with the annihilation they come with;
given them, both halves of the conclusion hold globally, and no cover need be chosen or cut down
by hand. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover
    (ψ : ∀ V : X.affineOpens, G.obj ⋙ Scheme.Modules.restrictFunctor V.1.ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor V.1.ι)
    (hψ : ∀ (V W : X.affineOpens) (n : ℕᵒᵖ) (O : X.Opens) (hOV : O ≤ V.1) (hOW : O ≤ W.1),
      localAppOpen V.1 ((ψ V).app n) hOV = localAppOpen W.1 ((ψ W).app n) hOW)
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
            Functor.whiskerRight α (Scheme.Modules.restrictFunctor V.1.ι) = ψ V := by
  have hU : IsOpenCover fun V : X.affineOpens => V.1 :=
    IsOpenCover.mk (iSup_affineOpens_eq_top X)
  obtain ⟨α, hα, hres⟩ := exists_isDirectImageCharacterized_of_openCover π J G 𝓕 β
    (fun V : X.affineOpens => V.1) hU ψ hψ hchar
  refine ⟨α, hα, ?_, hres⟩
  refine isKernelCokernelAnnihilatedByPower_of_affineOpens K α fun V => ?_
  exact (hres V).symm ▸ hann V

end Locality

end Stacks.Coherent

end
