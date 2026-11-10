module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.IdealSmul
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.Cohomology.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FinitePushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing

/-!
# [Stacks, Tag 01YP] as an equality of subsheaves, and the vanishing it supplies

For an affine morphism `f : Y ⟶ X`, a quasi-coherent `𝒪_Y`-module `ℱ` and a quasi-coherent
sheaf of ideals `𝒥` on `X`, [Stacks, Tag 01YP] says `𝒥 · f₊ℱ = f₊((f⁻¹𝒥) · ℱ)`. That identity
is already in the library as
`Stacks.AlgebraicGeometry.AffineIdealPushforward.ideal_smul_pushforward_sections_eq`, but **only
as an equality of submodules of sections over each affine open**, which is not a statement about
the two subsheaves and in particular does not say that `𝒥 · f₊ℱ` is a direct image. This promotes
it, and draws the consequence the dévissage of [Stacks, Tag 01YM] needs: for `Y` affine,
`Hᵖ(X, 𝒥 · f₊ℱ) = 0` for every `p > 0`.

The promotion rests on two general facts proved here, neither of which was in the repository or
in Mathlib (`mathlib_search` for both; see the implementation notes).

* A `SheafOfModules.Submodule` of a module sheaf on a scheme is **determined by its sections
  over affine opens** (`submodule_ext_affineOpens`). Membership is a local condition and the
  affine opens are a basis, so nothing beyond the affine data is free.
* The sections of a submodule `N ⊆ M` over the inverse images `f ⁻¹ᵁ V` form a submodule
  `pushforwardSubmodule f N` of `f₊M`, and — this is the point —
  `(pushforwardSubmodule f N).toSheafOfModules` is *definitionally* `f₊(N.toSheafOfModules)`
  (`toSheafOfModules_pushforwardSubmodule`, proved by `rfl`). So a subsheaf identified with a
  `pushforwardSubmodule` **is** a direct image, with no transport.

## Main definitions

* `Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.pushforwardSubmodule`: the subsheaf
  `f₊N ⊆ f₊M` attached to a subsheaf `N ⊆ M`.

## Main results

* `mem_of_forall_affineOpens`: a section of `M` over `V` lies in a submodule `N` as soon as all
  of its restrictions to affine opens inside `V` do.
* `submodule_ext_affineOpens`: two submodules of `M` with the same sections over every affine
  open are equal.
* `toSheafOfModules_pushforwardSubmodule`, `ι_pushforwardSubmodule`: the sheaf attached to
  `pushforwardSubmodule f N` is `f₊(N.toSheafOfModules)` and its inclusion is `f₊` of the
  inclusion of `N`, both on the nose.
* `idealPowSmul_pushforward_eq`: **[Stacks, Tag 01YP] as an equality of subsheaves of `f₊ℱ`**,
  `𝒥 · f₊ℱ = f₊((f⁻¹𝒥) · ℱ)`, for `f` affine.
* `isZero_hgroup_idealPowSmul_pushforward`: **the vanishing** `Hᵖ(X, 𝒥 · f₊ℱ) = 0` for `p > 0`,
  `f` affine and `Y` affine.
* `isCoherent_idealPowSmul_pushforward`: `𝒥 · f₊ℱ` is coherent, for `f` finite, `X` locally
  Noetherian and `ℱ` coherent — proved through the direct image rather than through
  [Stacks, Tag 01YG]'s Noetherian hypothesis on `X`, so no `IsNoetherian X` is needed.

## What this is for, and what it does *not* settle

[Stacks, Tag 01YQ] is open and no attribute is attached here.
`Stacks.AlgebraicGeometry.Tag01YQDevissage.isAffine_of_isFinite_surjective_of_hgeneric`
reduces it to [Stacks, Tag 01YE], [Stacks, Tag 01YL] and clause (3) of [Stacks, Tag 01YM] for
`H¹`, and records the residue inside clause (3) as *promoting [Stacks, Tag 01YP] from an equality
of section submodules on each affine open to the isomorphism of module sheaves that
[Stacks, Tag 089W] consumes*. `idealPowSmul_pushforward_eq` together with
`toSheafOfModules_pushforwardSubmodule` is that promotion, and
`isZero_hgroup_idealPowSmul_pushforward` is the statement it was wanted for.

Two corrections to that record.

1. **No isomorphism of module sheaves is needed at all.** The identification is an *equality* of
   subsheaves, and the right-hand side is a direct image by `rfl`; so the vanishing transports
   along `congrArg`, with no comparison morphism to build and nothing to prove natural.
2. **Clause (3)(c) does not require the equality, only the inclusion `f₊((f⁻¹𝒥)·ℱ) ⊆ 𝒥 · f₊ℱ`**,
   because the clause asks for *some* coherent submodule `𝒢' ⊆ 𝒢` whose sections over an affine
   open lie in `𝒥(U) · Γ(𝒢, U)`, not for `𝒥 · 𝒢` itself. Choosing
   `𝒢' := pushforwardSubmodule f ((f⁻¹𝒥) · ℱ)` makes (3)(c)'s coherence and `H¹`-vanishing
   clauses immediate from the two results below and needs only one direction of
   [Stacks, Tag 01YP]. Both choices of `𝒢'` are available after this file; the equality is
   proved because it is the statement of the tag.

What remains owed in clause (3), and is *not* done here, is the stalk clause: surjectivity at the
generic point `ξ` of `(𝒢')_ξ → 𝒢_ξ` for `ξ ∉ 𝒥.support`, together with the support clause
`x ∈ I.support ↔ Nontrivial (𝒢.presheaf.stalk x)` coming out of [Stacks, Tag 01YO]. Tags
[Stacks, Tag 01YE] and [Stacks, Tag 01YL] are untouched.

## Implementation notes

**`mathlib_search` negatives.** "a subsheaf of modules on a scheme is determined by its sections
on affine opens" returns only the `SheafOfModules.Submodule` API itself (`ext` from equality of
the underlying presheaf submodule, the lattice operations) and `Scheme.Modules.isSheaf`; nothing
affine-local. "ideal sheaf times pushforward equals pushforward of inverse image ideal times
module affine morphism" returns only `Scheme.IdealSheafData.ideal_map`,
`ideal_map_of_isAffineHom` and the Galois connection `map_gc`; Mathlib has no `comap` analogue of
`ideal_map_of_isAffineHom` and no statement about `𝒥 · f₊ℱ`.

**Why `pushforwardSubmodule`'s sheaf is a direct image definitionally.**
`Scheme.Modules.pushforward_obj_obj` and `pushforward_obj_presheaf_map` are both `rfl`, and
`PresheafOfModules.Submodule.toPresheafOfModules` takes `obj X` to `ModuleCat.of _ (N.obj X)`
pointwise. Writing the carrier of `pushforwardSubmodule f N` over `V` as the *set* of sections of
`f₊M` lying in `N (f ⁻¹ᵁ V)` therefore produces the same presheaf of modules as pushing
`N.toSheafOfModules` forward. The scalar restriction along `f.app V` is invisible for the same
reason: `smul_mem'` is discharged by `(N.toSubmodule.obj _).smul_mem ((f.app V).hom c)`.

**The locality axiom of the pushforward submodule** is proved by transporting the covering sieve:
a cover of `V` by opens on which the section lies in `N` after pulling back gives the cover
`{f ⁻¹ᵁ W}` of `f ⁻¹ᵁ V`, and `N.isSheaf` closes it. No quasi-coherence is used, so
`pushforwardSubmodule` is available for an arbitrary morphism of schemes.

**The cast in the library's [Stacks, Tag 01YP] is inert.** Its right-hand side transports a section
along `Equiv.cast (congrArg _ (Scheme.Modules.pushforward_obj_obj f ℱ U))`; that equality of types
is proved by `rfl`, so by proof irrelevance the transport is the identity and
`idealPowSmul_pushforward_eq` needs no coercion lemma for it.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
* [Stacks Project, Tag 01YP](https://stacks.math.columbia.edu/tag/01YP)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}}

/-! ### A submodule of a module sheaf on a scheme is affine-locally determined -/

/-- **Membership in a submodule of a module sheaf is affine-local.** If every restriction of
`s : Γ(M, V)` to an affine open inside `V` lies in `N`, then `s` lies in `N`. -/
theorem mem_of_forall_affineOpens {M : X.Modules} (N : M.Submodule) {V : X.Opens} (s : Γ(M, V))
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ V),
      M.presheaf.map (homOfLE hW).op s ∈ N.toSubmodule.obj (op W.1)) :
    s ∈ N.toSubmodule.obj (op V) := by
  refine N.isSheaf s fun x hx ↦ ?_
  obtain ⟨-, ⟨W, hWaff, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact ⟨W, homOfLE hWle, h ⟨W, hWaff⟩ hWle, hxW⟩

/-- Inclusion of submodules of a module sheaf can be checked on sections over affine opens. -/
private theorem le_of_forall_affineOpens {M : X.Modules} {N₁ N₂ : M.Submodule}
    (h : ∀ U : X.affineOpens, N₁.toSubmodule.obj (op U.1) ≤ N₂.toSubmodule.obj (op U.1)) :
    N₁ ≤ N₂ := by
  refine PresheafOfModules.Submodule.le_iff.2 fun V s hs ↦ ?_
  obtain ⟨V⟩ := V
  exact mem_of_forall_affineOpens N₂ s fun W hW ↦ h W (N₁.toSubmodule.map_mem (homOfLE hW).op hs)

/-- **A submodule of a module sheaf on a scheme is determined by its sections over the affine
opens.** -/
theorem submodule_ext_affineOpens {M : X.Modules} {N₁ N₂ : M.Submodule}
    (h : ∀ U : X.affineOpens, N₁.toSubmodule.obj (op U.1) = N₂.toSubmodule.obj (op U.1)) :
    N₁ = N₂ :=
  le_antisymm (le_of_forall_affineOpens fun U ↦ (h U).le)
    (le_of_forall_affineOpens fun U ↦ (h U).ge)

/-! ### The direct image of a subsheaf -/

/-- **The direct image `f₊N ⊆ f₊M` of a subsheaf `N ⊆ M`.** Over an open `V` its sections are
the sections of `N` over `f ⁻¹ᵁ V`, which are sections of `f₊M` over `V` on the nose. -/
def pushforwardSubmodule (f : Y ⟶ X) {M : Y.Modules} (N : M.Submodule) :
    ((Scheme.Modules.pushforward f).obj M).Submodule where
  toSubmodule :=
    { obj V :=
        { carrier := {s : Γ((Scheme.Modules.pushforward f).obj M, V.unop) |
            (s : Γ(M, f ⁻¹ᵁ V.unop)) ∈ N.toSubmodule.obj (op (f ⁻¹ᵁ V.unop))}
          add_mem' := fun ha hb ↦ (N.toSubmodule.obj (op (f ⁻¹ᵁ V.unop))).add_mem ha hb
          zero_mem' := (N.toSubmodule.obj (op (f ⁻¹ᵁ V.unop))).zero_mem
          smul_mem' := fun c _ hx ↦ (N.toSubmodule.obj (op (f ⁻¹ᵁ V.unop))).smul_mem
            ((f.app V.unop).hom c) hx }
      map := fun {V _} i s hs ↦ N.toSubmodule.map_mem ((Opens.map f.base).map i.unop).op hs }
  isSheaf := by
    intro V s hs
    refine N.isSheaf (X := op (f ⁻¹ᵁ V.unop)) s fun y hy ↦ ?_
    obtain ⟨W, g, hg, hyW⟩ := hs (f.base y) hy
    exact ⟨f ⁻¹ᵁ W, homOfLE fun z hz ↦ g.le hz, hg, hyW⟩

/-- The sections of `f₊N` over `V` are the sections of `N` over `f ⁻¹ᵁ V`. -/
theorem mem_pushforwardSubmodule (f : Y ⟶ X) {M : Y.Modules} (N : M.Submodule) (V : X.Opens)
    (s : Γ((Scheme.Modules.pushforward f).obj M, V)) :
    s ∈ (pushforwardSubmodule f N).toSubmodule.obj (op V) ↔
      (s : Γ(M, f ⁻¹ᵁ V)) ∈ N.toSubmodule.obj (op (f ⁻¹ᵁ V)) :=
  Iff.rfl

/-- **The sheaf attached to `f₊N` is the direct image of the sheaf attached to `N`**, on the
nose. This is what makes an identification with a `pushforwardSubmodule` usable: the subsheaf
*is* a direct image, so results about direct images apply to it with no transport. -/
theorem toSheafOfModules_pushforwardSubmodule (f : Y ⟶ X) {M : Y.Modules} (N : M.Submodule) :
    (pushforwardSubmodule f N).toSheafOfModules =
      (Scheme.Modules.pushforward f).obj N.toSheafOfModules :=
  rfl

/-- The inclusion of `f₊N` into `f₊M` is the direct image of the inclusion of `N` into `M`. -/
theorem ι_pushforwardSubmodule (f : Y ⟶ X) {M : Y.Modules} (N : M.Submodule) :
    (pushforwardSubmodule f N).ι = (Scheme.Modules.pushforward f).map N.ι :=
  rfl

/-! ### [Stacks, Tag 01YP] as an equality of subsheaves -/

/-- **[Stacks, Tag 01YP], as an equality of subsheaves of `f₊ℱ`.** For an affine morphism
`f : Y ⟶ X`, a quasi-coherent `ℱ` and a quasi-coherent sheaf of ideals `𝒥` on `X`,

    𝒥 · f₊ℱ = f₊((f⁻¹𝒥) · ℱ)

as submodules of `f₊ℱ`. The library's form of the tag is the equality of the two submodules of
sections over each *affine* open; `submodule_ext_affineOpens` is exactly what upgrades that to the
subsheaves, since both sides are submodules of one module sheaf.

No attribute is attached: the tag is already carried by
`Stacks.AlgebraicGeometry.AffineIdealPushforward.ideal_smul_pushforward_sections_eq`, which this
result is deduced from. -/
theorem idealPowSmul_pushforward_eq (f : Y ⟶ X) [IsAffineHom f] (J : X.IdealSheafData)
    (ℱ : Y.Modules) [ℱ.IsQuasicoherent] :
    IdealPowerSmul.idealPowSmul J 1 ((Scheme.Modules.pushforward f).obj ℱ) =
      pushforwardSubmodule f (IdealPowerSmul.idealPowSmul (J.comap f) 1 ℱ) := by
  refine submodule_ext_affineOpens fun U ↦ ?_
  have hpre : (IdealPowerSmul.idealPowSmul (J.comap f) 1 ℱ).toSubmodule.obj (op (f ⁻¹ᵁ U.1)) =
      (J.comap f).ideal ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ ^ 1 •
        (⊤ : Submodule Γ(Y, f ⁻¹ᵁ U.1) Γ(ℱ, f ⁻¹ᵁ U.1)) :=
    IdealPowerSmul.obj_idealPowSmul (J.comap f) 1 ℱ ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  refine SetLike.ext fun s ↦ ?_
  rw [IdealPowerSmul.obj_idealPowSmul J 1 ((Scheme.Modules.pushforward f).obj ℱ) U, pow_one]
  change _ ↔ (s : Γ(ℱ, f ⁻¹ᵁ U.1)) ∈
    (IdealPowerSmul.idealPowSmul (J.comap f) 1 ℱ).toSubmodule.obj (op (f ⁻¹ᵁ U.1))
  rw [hpre, pow_one]
  exact Set.ext_iff.mp (AffineIdealPushforward.ideal_smul_pushforward_sections_eq f J ℱ U) s

/-! ### The two consequences the dévissage of [Stacks, Tag 01YM] asks for -/

/-- **`Hᵖ(X, 𝒥 · f₊ℱ) = 0` for `p > 0`**, when `f : Y ⟶ X` is affine and `Y` is affine.

By `idealPowSmul_pushforward_eq` the subsheaf `𝒥 · f₊ℱ` is the direct image of
`(f⁻¹𝒥) · ℱ`, and that module is quasi-coherent on the affine scheme `Y`, so its own higher
cohomology vanishes by [Stacks, Tag 01XB] and the direct image's agrees with it by
[Stacks, Tag 089W]. -/
theorem isZero_hgroup_idealPowSmul_pushforward
    (f : Y ⟶ X) [IsAffineHom f] [IsAffine Y] (J : X.IdealSheafData) (ℱ : Y.Modules)
    [ℱ.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p (IdealPowerSmul.idealPowSmul J 1
      ((Scheme.Modules.pushforward f).obj ℱ)).toSheafOfModules) := by
  have : (IdealPowerSmul.idealPowSmul (J.comap f) 1 ℱ).toSheafOfModules.IsQuasicoherent :=
    IdealPowerSmul.isQuasicoherent_idealPowSmul (J.comap f) 1 ℱ
  have hiso := AffineCohomologyPushforward.cohomologyPushforwardIsoApp f p
    (IdealPowerSmul.idealPowSmul (J.comap f) 1 ℱ).toSheafOfModules
  rw [idealPowSmul_pushforward_eq f J ℱ, toSheafOfModules_pushforwardSubmodule]
  exact IsZero.of_iso (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine Y _ p hp) hiso.symm

/-- **`𝒥 · f₊ℱ` is coherent**, for `f : Y ⟶ X` finite, `X` locally Noetherian and `ℱ` coherent.

This goes through the direct image rather than through
`Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_idealPowSmul`, which asks `IsNoetherian X`;
here `IsLocallyNoetherian X` suffices, because `(f⁻¹𝒥) · ℱ` is coherent on `Y` — Noetherian, being
affine of finite type over a locally Noetherian base — and a finite direct image of a coherent
module is coherent by [Stacks, Tag 01Y6]. -/
theorem isCoherent_idealPowSmul_pushforward (f : Y ⟶ X) [IsFinite f] [IsAffine Y]
    [IsLocallyNoetherian X] (J : X.IdealSheafData) (ℱ : Y.Modules) [ℱ.IsQuasicoherent]
    [ℱ.IsCoherent] :
    (IdealPowerSmul.idealPowSmul J 1
      ((Scheme.Modules.pushforward f).obj ℱ)).toSheafOfModules.IsCoherent := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian Y := ⟨⟩
  have : (IdealPowerSmul.idealPowSmul (J.comap f) 1 ℱ).toSheafOfModules.IsQuasicoherent :=
    IdealPowerSmul.isQuasicoherent_idealPowSmul (J.comap f) 1 ℱ
  have : (IdealPowerSmul.idealPowSmul (J.comap f) 1 ℱ).toSheafOfModules.IsCoherent :=
    IdealPowerSmul.isCoherent_idealPowSmul (J.comap f) 1 ℱ
  rw [idealPowSmul_pushforward_eq f J ℱ, toSheafOfModules_pushforwardSubmodule]
  exact FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f _

end Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf

end
