module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiAffineSource.Basic

/-!
# Stacks Tag 0892 part (2): ampleness pulls back along a quasi-affine morphism

Stacks Tag 0892 has two parts. Part (1): if `L` is ample relative to `f : X ⟶ S` and `M` is an
ample invertible `𝒪_S`-module, then `L ⊗ f^* M ^⊗ a` is ample for all large `a`. Part (2): if `M`
is ample and `f` is quasi-affine then `f^* M` is ample.

This file proves **part (2) from a single named premise**,
`Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow`, which is the surjectivity half of [Stacks, Tag
01PW] for the structure sheaf. It also records part (2) for an *affine* morphism, which needs no
premise at all and is already a theorem of this repository.

## Main definitions

* `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow`: the premise. For `s` a global section of a
  positive tensor power of an invertible `L` and `g` a section of `𝒪_X` over the nonvanishing open
  `X_s`, the basic open `X.basicOpen g` is itself the nonvanishing open of a global section of a
  positive tensor power of `L`.

## Main results

* `Stacks.AmpleQuasiAffinePullback.basicOpenIsPowNonvanishing`: the premise implies
  `Stacks.AmplePullback.BasicOpenIsPowNonvanishing`, the premise on which the general case of Stacks
  Tag 0B3E and clause (1) ⟹ (3) of Stacks Tag 01Q3 already stand. So it is one input for the whole
  cluster, not a second one.
* `Stacks.AmpleQuasiAffinePullback.exists_isAffineOpen_basicOpen_of_isQuasiAffine`: every point of a
  quasi-affine open subscheme lies in an affine basic open of a section of `𝒪_X` over that open.
  Unconditional.
* `Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isQuasiAffineHom`: **Stacks Tag 0892
  part (2) on the premise.**
* `isAmple_modulePullback_of_isAmple_modulePullback_tensorPowModule`: the step the
  source attributes to Stacks Tag 01PT, discharged unconditionally. If the pullback of a positive
  tensor power of `M` is ample then so is the pullback of `M`.
* `Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom`: **Stacks Tag 0892 part
  (2) for an affine morphism, with no premise**, in the shape of the tagged statement.

## The route, and why it is not the source's

The source proves part (2) from part (1): a quasi-affine `f` makes `𝒪_X` relatively ample (Stacks
Tag 0891), part (1) then gives ampleness of `𝒪_X ⊗ f^* M ^⊗ a = (f^* M) ^⊗ a` for large `a`, and
Stacks Tag 01PT descends that to `f^* M`. The route below avoids part (1) entirely, and so avoids
everything part (1) needs beyond Tag 01PW.

Let `x : X`. Ampleness of `M` gives `m ≥ 1` and `t ∈ Γ(S, M ^⊗ m)` with `S_t` affine and
containing `f x`. Stacks Tag 0H78 — here
`Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection` — identifies the nonvanishing open of
the pulled-back section `f^* t` of `(f^* M) ^⊗ m` with `f⁻¹(S_t)`, which is a **quasi-affine
scheme** because `f` is quasi-affine and `S_t` is affine. Quasi-affineness puts an affine basic open
of a section `g` of `𝒪_X` over `f⁻¹(S_t)` through `x`, and the premise turns that basic open into
the nonvanishing open of a global section of a power of `f^* M`. That is ampleness of `f^* M`.

The affine case needs none of this: there `f⁻¹(S_t)` is affine on the nose, so the pulled-back
section already has an affine nonvanishing open and no shrinking is required. That case is
`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01SK](https://stacks.math.columbia.edu/tag/01SK)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)

## What is not done

**Neither label of Tag 0892 is closed, and nothing here carries the tag.**

*Part (2)* stands on `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow`, a hypothesis the tagged
statement does not have, so the label is not attached. The premise is not avoidable by a
better choice of section: the global sections of `(f^* M) ^⊗ k` that `f` and `M` supply by
themselves are the pulled-back ones, and their nonvanishing opens are the preimages `f⁻¹(S_t)`,
which are quasi-affine and **not affine** whenever `f` is not affine. Producing a global section
that is not a pullback *is* the content of Tag 01PW.

*Part (1)* is not proved here. Its proof needs Tag 01PW for a **module-valued** `F`, which the
premise above does not give, together with two comparison isomorphisms. The four missing
ingredients, stated so that they can be built:

* `Tag 01PW surjectivity, module-valued`: for `X` quasi-compact and quasi-separated, `N` and `F`
  invertible `𝒪_X`-modules, `σ : Γ(N, ⊤)` and a section `s` of `F` over the nonvanishing open
  `X_σ`, there are `e ≥ 1` and `s' : Γ(F ⊗ N ^⊗ e, ⊤)` whose restriction to `X_σ` is `s ⊗ σ ^ e`.
  It would live next to `Stacks.AmplePullback.BasicOpenIsPowNonvanishing`, which is its `F = 𝒪_X`
  case; the premise of this file is that case with the affineness hypothesis dropped. Nothing in the
  repository proves either: `AmpleTheory/Basic.lean`, `AmpleEventualGeneration/Basic.lean` and
  `AmpleAffineAvoidance/AmpleFiniteSet.lean` each record Tag 01PW as the keystone it lacks.
* `(A ⊗ B) ^⊗ ν ≅ A ^⊗ ν ⊗ B ^⊗ ν` for `A B : X.Modules` invertible, in the
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling of
  `../RelativeVeryAmple/TensorPower.lean`, where `Stacks.RelativeVeryAmple.tensorPowModulePowIso` is
  the analogous `(A ^⊗ d) ^⊗ ν ≅ A ^⊗ (d ν)`.
* `Γ((modulePullback U.ι.toLRSHom.toShHom).obj G, ⊤) ≅ Γ(G, U)` for `U : X.Opens` — restriction
  along an open immersion computes sections. `Stacks.NonvanishingPullback.pullbackGlobalSection`
  is the forward map for an arbitrary morphism; the inverse for an open immersion is what turns
  the ampleness that `Stacks.RelativeAmple.IsRelativelyAmple` asserts on the subscheme `f⁻¹V`
  into sections of `L ^⊗ n` over the open `f⁻¹V` of `X`, which is the form Tag 01PW consumes.
* Quasi-separatedness of `X`, which Tag 01PW needs: in the source it comes from Properties of
  Schemes, Lemma 28.27.8 (an ample module makes the scheme separated) and Morphisms, Lemma 29.38.3
  (a relatively ample module makes the morphism separated). Neither is in this repository. Stacks
  Tag 01PV, `Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`
  (`U` affine implies `U ⊓ X_s` affine), makes the pairwise intersections of the affine cover that
  ampleness supplies affine, hence quasi-compact; but `QuasiSeparatedSpace.of_isTopologicalBasis`
  asks for a **basis** of such opens, and that the affine `X_s` form a basis is clause (4) of
  Stacks Tag 01Q3, also unproved here. The same hypothesis is needed to discharge the premise
  above, so part (2) is not free of it either — only of everything else.

**The source's own crossing step for part (1) is not needed.** The source proves ampleness only
for `a` "sufficiently divisible and large" and then crosses to all large `a` using that `M ^⊗ c`
is globally generated for `c ≫ 0` (Properties of Schemes, Proposition 28.27.13) together with
Lemma 28.27.5. The divisibility is an artefact of keeping the exponent of `L` fixed: the section
`s` of `L ^⊗ n` over `f⁻¹(S_t)` may be replaced by `s ^ m`, a section of `L ^⊗ (n m)` with the same
nonvanishing locus, and then `L ^⊗ (n m) ⊗ (f^* M) ^⊗ (m (e + b))` is the `(n m)`-th power of
`L ⊗ f^* M ^⊗ a` exactly when `e + b = a n`, which is solvable with `b ≥ 1` for **every**
`a ≥ e + 1` and needs no divisibility. So part (1) follows from the four ingredients above alone; it
does not also need Proposition 28.27.13 and Tag 01Q1, contrary to what
`../AmplePullback/QuasiAffineUnitIso.lean` suggests.

**Two remarks.**

* `../AmplePullback/QuasiAffineUnitIso.lean` says part (2) in general "needs, as in the
  source, part (1)
  together with Stacks Tag 01PT (`L` is ample if and only if `L ^⊗ n` is, for `n ≥ 1`)".
  The half of Tag 01PT that
  the source's route consumes is **available and unconditional**:
  `Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule`
  (`../RelativeVeryAmple/TensorPower.lean`) is exactly `IsAmple X (L ^⊗ d) → IsAmple X L` for
  `d ≥ 1`. It carries no Tag 01PT attribute, but
  the mathematics is there.
* The same file says part (2) is proved here only "for an invertible module isomorphic to `𝒪_S`".
  Part (2) is in fact already proved in this repository **for every affine morphism and every
  ample `M`**, by `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`, which is
  unconditional; `Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom` below is
  that statement in the spelling of Tag 0892. The unit-isomorphic case of `../AmplePullback/` is not
  the frontier of part (2); the frontier is "quasi-affine but not affine".
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleQuasiAffinePullback

/-! ### An affine basic open inside a quasi-affine open -/

/-- **Every point of a quasi-affine open subscheme lies in an affine basic open of a section of
`𝒪_X` over that open.** Unconditional, and the only geometric input of part (2) besides the
premise.

Quasi-affineness of `U` says that the basic opens of global sections of `U` which are affine form
a basis of `U`; `AlgebraicGeometry.Scheme.Opens.ι_image_basicOpen'` reads such a basic open as a
basic open of `X` of a section over `U`, and
`AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion` moves the affineness across the
open immersion. No extension to a *global* section is performed, and none is possible: that is the
premise. -/
theorem exists_isAffineOpen_basicOpen_of_isQuasiAffine {X : Scheme.{u}} (U : X.Opens)
    (hU : U.toScheme.IsQuasiAffine) {x : X} (hx : x ∈ U) :
    ∃ g : Γ(X, U), IsAffineOpen (X.basicOpen g) ∧ x ∈ X.basicOpen g := by
  have := hU
  obtain ⟨-, ⟨-, ⟨t, ht, rfl⟩, rfl⟩, hxt, -⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen U.toScheme).exists_subset_of_mem_open
      (Set.mem_univ (⟨x, hx⟩ : U.toScheme)) isOpen_univ
  have himg := Scheme.Opens.ι_image_basicOpen' (U := U) t
  refine ⟨X.presheaf.map (eqToHom U.ι_image_top.symm).op t, ?_, ?_⟩
  · rw [← himg, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
    exact ht
  · rw [← himg]
    exact ⟨⟨x, hx⟩, hxt, rfl⟩

/-! ### The premise -/

/-- **The consequence of Stacks Tag 01PW that part (2) stands on.** For `s` a global section of a
positive tensor power of `L` and `g` a section of `𝒪_X` over the nonvanishing open `X_s`, the basic
open `X.basicOpen g` is the nonvanishing open of a global section of a positive tensor power of
`L`.

This is `Stacks.AmplePullback.BasicOpenIsPowNonvanishing` **with its affineness hypothesis on `X_s`
removed**, and the removal is what part (2) needs: the open it has to shrink inside is a preimage
`f⁻¹(S_t)`, which quasi-affineness of `f` makes quasi-affine and not affine. Tag 01PW itself
carries no affineness hypothesis either — it asks only that `X` be quasi-compact and
quasi-separated — so this is the faithful consequence of the source lemma, and
`Stacks.AmpleQuasiAffinePullback.basicOpenIsPowNonvanishing` records that it is the stronger
premise. -/
def BasicOpenIsPow (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
    ∀ g : Γ(X, powNonvanishingOpen X L n s), ∃ m : ℕ, 1 ≤ m ∧
      ∃ t : Γ(tensorPowModule X L (m : ℤ), ⊤),
        powNonvanishingOpen X L m t = X.basicOpen g

/-- **The premise of this file implies the premise of Stacks Tag 0B3E**, hence also clause
(1) ⟹ (3) of Stacks Tag 01Q3 through `Stacks.AmplePullback.isBasisNonvanishing_of_isAmple`. So
proving `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow` closes the general case of Tag 0B3E, clause
(3) of Tag 01Q3 and part (2) of Tag 0892 at once; it is not a new input but a strengthening of the
existing one. -/
theorem basicOpenIsPowNonvanishing (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (h : BasicOpenIsPow X L) : Stacks.AmplePullback.BasicOpenIsPowNonvanishing X L :=
  fun n hn s _ g => h n hn s g

/-! ### Part (2) -/

section Part2

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules) [IsInvertibleModule S M]

/-- **Stacks Tag 0892 part (2), on the premise `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow`.**
The pullback of an ample invertible module along a quasi-affine morphism is ample.

`X` is quasi-compact because `f` is (Stacks Tag 01SL) and `S` is. For a point `x`, ampleness of
`M` gives `m ≥ 1` and `t` with `S_t` affine through `f x`; Stacks Tag 0H78 identifies the
nonvanishing open of `f^* t` with `f⁻¹(S_t)`, which is quasi-affine; and
`Stacks.AmpleQuasiAffinePullback.exists_isAffineOpen_basicOpen_of_isQuasiAffine` followed by the
premise produces an affine nonvanishing open of a global section of a power of `f^* M` through `x`.
-/
theorem isAmple_modulePullback_of_isQuasiAffineHom [IsQuasiAffineHom f]
    (hext : BasicOpenIsPow X ((modulePullback f.toLRSHom.toShHom).obj M))
    (hM : IsAmple S M) :
    IsAmple X ((modulePullback f.toLRSHom.toShHom).obj M) := by
  have hS : CompactSpace S := Stacks.Ample.IsAmple.compactSpace S M hM
  have hX : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  refine (isAmple_iff_forall_affine_nonvanishingOpen X _).mpr ⟨hX, fun x => ?_⟩
  obtain ⟨m, hm, t, haff, hfx⟩ := IsAmple.exists_affine_nonvanishingOpen S M hM (f.base x)
  have heq := Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection f M m t
  have hqa : (powNonvanishingOpen X ((modulePullback f.toLRSHom.toShHom).obj M) m
      (Stacks.NonvanishingPullback.pullbackPowSection f M m t)).toScheme.IsQuasiAffine := by
    rw [heq]
    exact IsQuasiAffineHom.isQuasiAffine_preimage _ haff
  have hx : x ∈ powNonvanishingOpen X ((modulePullback f.toLRSHom.toShHom).obj M) m
      (Stacks.NonvanishingPullback.pullbackPowSection f M m t) := by
    rwa [heq]
  obtain ⟨g, hgaff, hxg⟩ := exists_isAffineOpen_basicOpen_of_isQuasiAffine _ hqa hx
  obtain ⟨m', hm', t', ht'⟩ := hext m hm _ g
  exact ⟨m', hm', t', by rwa [ht'], by rwa [ht']⟩

/-- **The step of the source's proof of part (2) that it attributes to Stacks Tag 01PT, discharged
unconditionally.** If the pullback of *some* positive tensor power of `M` is ample, then so is the
pullback of `M`.

This is what part (1) hands to part (2) in the source: part (1) applied to `L = 𝒪_X` makes
`𝒪_X ⊗ f^* M ^⊗ a` ample for large `a`, and this reduces that to `f^* M`.
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` moves the power across the pullback and
`Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule` — the half of Tag 01PT the argument
uses — descends it. So no unproved input of Tag 0892 is Tag 01PT. -/
theorem isAmple_modulePullback_of_isAmple_modulePullback_tensorPowModule (a : ℕ) (ha : 1 ≤ a)
    (h : IsAmple X ((modulePullback f.toLRSHom.toShHom).obj (tensorPowModule S M (a : ℤ)))) :
    IsAmple X ((modulePullback f.toLRSHom.toShHom).obj M) :=
  Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule _ a ha
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _
      (hN' := isInvertibleModule_tensorPowModule _ _ (a : ℤ))
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f M a)).mp h)

/-- **Stacks Tag 0892 part (2) for an affine morphism, with no premise**, in the shape of the
tagged statement. This is `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`, whose module
`Stacks.AmpleLocallyClosed.pullbackModule f M` is the statement's
`(modulePullback f.toLRSHom.toShHom).obj M` as an `abbrev`.

An affine morphism is quasi-affine (`Stacks.QuasiAffineSource.isQuasiAffineHom_of_isAffineHom`), so
this is a special case of part (2); it is recorded because it needs nothing from Tag 01PW. -/
theorem isAmple_modulePullback_of_isAffineHom [IsAffineHom f] (hM : IsAmple S M) :
    IsAmple X ((modulePullback f.toLRSHom.toShHom).obj M) :=
  Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom f M hM

end Part2

end Stacks.AmpleQuasiAffinePullback

end
