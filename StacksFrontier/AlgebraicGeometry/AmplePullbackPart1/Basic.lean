module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Restriction
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers

/-!
# Stacks Tag 0892 part (1), reduced to Stacks Tag 01PW for a module-valued coefficient

Part (1) of [Stacks, Tag 0892]: if `L` is ample relative to `f : X ⟶ S` and `M` is an ample
invertible `𝒪_S`-module, then `L ⊗ f^* M ^⊗ a` is ample for every sufficiently large `a`.

This file does everything part (1) needs **except** [Stacks, Tag 01PW] for a module-valued
coefficient, and isolates that one input as a hypothesis.

## Main definitions

* `Stacks.AmplePullbackPart1.tensorPullbackPowModule`: `L ⊗ f^* (M ^⊗ a)`, the module part (1)
  concludes about.
* `Stacks.AmplePullbackPart1.tensorPullbackSplitModule`: `L ^⊗ k ⊗ (f^* M) ^⊗ (a k)`, the module
  its `k`-th tensor power is isomorphic to.
* `Stacks.AmplePullbackPart1.tensorPullbackPowIso`: **that isomorphism**,
  `(L ⊗ f^* M ^⊗ a) ^⊗ k ≅ L ^⊗ k ⊗ (f^* M) ^⊗ (a k)`.
* `Stacks.AmplePullbackPart1.EventualAffineDatum`: **the pointwise datum part (1) is equivalent
  to.** For every point `x` there are a threshold `e` and an affine open `V ∋ x` such that for
  every `a ≥ e` some positive tensor power `L ^⊗ k ⊗ (f^* M) ^⊗ (a k)` carries a global section
  whose nonvanishing open is exactly `V`.

## Main results

* `Stacks.AmplePullbackPart1.isAmple_tensorPullbackPowModule_iff`: **the target shape.** For a
  fixed `a`, ampleness of `L ⊗ f^* M ^⊗ a` is precisely quasi-compactness of `X` together with:
  every point lies in an affine nonvanishing open of a global section of
  `L ^⊗ k ⊗ (f^* M) ^⊗ (a k)` for some `k ≥ 1`. This is the form in which the output of Tag 01PW is
  consumed.
* `Stacks.AmplePullbackPart1.exists_threshold_isAmple`: **part (1) from the pointwise datum.**
  The datum, plus quasi-compactness of `X`, gives a single threshold `n` with
  `L ⊗ f^* M ^⊗ a` ample for every `a ≥ n`. This is the `∃ n, ∀ a ≥ n` of the statement of Tag 0892,
  and the only place compactness of `X` is used.
* `Stacks.AmplePullbackPart1.exists_isAmple_preimage_of_isRelativelyAmple`: **the geometric input
  of part (1), unconditionally.** For every `x : X` there are `m ≥ 1` and `t : Γ(M ^⊗ m, ⊤)` with
  `S_t` affine containing `f x`, with the nonvanishing open of the pulled-back section `f^* t`
  of `(f^* M) ^⊗ m` equal to `f⁻¹(S_t)`, and with `L` restricted to `f⁻¹(S_t)` ample. Those are
  exactly the hypotheses of Tag 01PW on `X` with `N = f^* M`, `σ = f^* t`.
* `Stacks.AmplePullbackPart1.compactSpace_of_isAmple`: `X` is quasi-compact whenever `S` carries
  an ample module and `f` is quasi-compact, which relative ampleness supplies.

* `Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`: **a scheme carrying an ample
  invertible module is quasi-separated**, with no premise. This is the fourth of the four ingredients
  that `StacksFrontier/AlgebraicGeometry/AmpleQuasiAffinePullback/Basic.lean` lists as missing; its
  stated obstacle, that clause (4) of [Stacks, Tag 01Q3] is "also unproved here", is false.

Of the four ingredients that file lists, the second is proved in the sibling file
`TensorPowerTensor.lean`, the third in `Restriction.lean`, and the fourth here. Only the first,
[Stacks, Tag 01PW] for a module-valued coefficient, is genuinely absent.

## Three claims of `AmpleQuasiAffinePullback/Basic.lean` that do not hold

That file's list of four missing ingredients for part (1) overstates what is missing, in three places.
The citations below are `file:line`.

1. Its fourth entry says that quasi-separatedness of `X` is out of reach because
   `QuasiSeparatedSpace.of_isTopologicalBasis` "asks for a **basis** of such opens, and that the
   affine `X_s` form a basis is clause (4) of Stacks Tag 01Q3, also unproved here". **Clause (4)
   is proved, with no premise**, as
   `Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple`
   (`../SectionExtension/AmpleConsumers.lean:119`), from
   `Stacks.SectionExtension.isSectionRatio_of_isAmple` (`../SectionExtension/Ample.lean:501`);
   clause (3) is `isBasisNonvanishing_of_isAmple` (`StacksFrontier/AlgebraicGeometry/SectionExtension/AmpleConsumers.lean:112`). The consequence is
   `Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple` below, three lines.
2. The same file says of `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow` and
   `Stacks.AmplePullback.BasicOpenIsPowNonvanishing` that "nothing in the repository proves
   either". **Both are proved from ampleness**:
   `Stacks.SectionExtension.basicOpenIsPow_of_isAmple` (`StacksFrontier/AlgebraicGeometry/SectionExtension/AmpleConsumers.lean:144`) and
   `basicOpenIsPowNonvanishing_of_isAmple` (`:149`). What remains open about them is only the case
   of a *non-ample* module, which is what part (2) needs.
3. Its third entry, the comparison `Γ(U.ι^* G, ⊤) ≅ Γ(G, U)`, is not missing either; see
   `Restriction.lean`.

**Where quasi-separatedness of `X` itself still stops.** `X` is quasi-separated as soon as `S` is
and `f` is a quasi-separated morphism, and both are available in substance: `S` is
quasi-separated by `Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple` applied to `M`, and
every `f⁻¹(V)` with `V ⊆ S` affine is quasi-separated by the same lemma applied to the restriction
of `L`, which is exactly the affine-local characterisation of
`AlgebraicGeometry.QuasiSeparated`. Assembling those two into `QuasiSeparatedSpace X` through
`AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` is **blocked by tooling, not by
mathematics**: at this Mathlib pin the instance
`HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)` cannot be synthesized
from outside its own file — Mathlib's own
`AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated` is itself preceded by
`set_option backward.isDefEq.respectTransparency.types false in` for that reason — and no new
`set_option` is used here. `AlgebraicGeometry.IsZariskiLocalAtTarget @QuasiSeparated` is not
synthesizable either, for the same reason. So the last step is one `set_option` away and is left
undone deliberately.

## The one missing input, precisely

The datum `Stacks.AmplePullbackPart1.EventualAffineDatum` is produced from the geometric input
above by the following argument, whose only unavailable step is Tag 01PW for a module-valued
coefficient.

Fix `x : X`. Let `m`, `t`, `U := f⁻¹(S_t)` and `σ := f^* t : Γ((f^* M) ^⊗ m, ⊤)` be as in
`Stacks.AmplePullbackPart1.exists_isAmple_preimage_of_isRelativelyAmple`, so `X_σ = U`.
Ampleness of `L|_U` gives `n ≥ 1` and a section of `L ^⊗ n` over `U` whose nonvanishing open
`V ⊆ U` is affine and contains `x`; replace it by its `m`-th power, a section `s` of
`L ^⊗ (n m)` over `U` with the same nonvanishing open. Then **Tag 01PW, applied with
`F = L ^⊗ (n m)` and `N = f^* M`**, produces `e ≥ 1` and a global section `s'` of
`L ^⊗ (n m) ⊗ (f^* M) ^⊗ (m e)` restricting on `U` to `s ⊗ σ ^ e`. Multiplying by `σ ^ b`
gives, for every `b ≥ 1`, a global section of `L ^⊗ (n m) ⊗ (f^* M) ^⊗ (m (e + b))` whose
nonvanishing open is `V` exactly: on `U` it is the nonvanishing open of `s`, and off `U` the
factor `σ` vanishes.

Taking `k = n m` and `a` with `a n = e + b` matches
`Stacks.AmplePullbackPart1.tensorPullbackSplitModule f L M a k`, since
`m (e + b) = m a n = a k`; and `b ≥ 1` is solvable for every `a ≥ e + 1`, because `n ≥ 1`. So
the threshold of the datum is `e + 1`. **The `m`-th power of the section is what removes the
divisibility condition** that the source's own proof carries, and with it the source's crossing
step through global generation of `M ^⊗ c`; this confirms the analysis in
`StacksFrontier/AlgebraicGeometry/AmpleQuasiAffinePullback/Basic.lean`.

So the shape needed is: for `X` quasi-compact and quasi-separated, `N` invertible, `σ` a global
section of `N ^⊗ m` with `m ≥ 1`, `F` invertible, and `s` a section of `F` over `X_σ`, there are
`e ≥ 1` and `s' : Γ(F ⊗ N ^⊗ (m e), ⊤)` with `s'|_{X_σ} = s ⊗ (σ ^ e)|_{X_σ}`. Note that `N` is
**not** assumed ample — `N = f^* M` and its ampleness is part (2), which the source deduces
*from* part (1). `Stacks.SectionExtension.isSectionRatio_of_isAmple` is the `F = 𝒪_X` case under
the additional hypothesis that `N` is ample, and
`Stacks.ModuleSectionExtension.exists_tensorSection_of_isAmple` is the module-valued case under
the same additional hypothesis; neither applies here, and dropping the ampleness of `N` is the
genuine content of Tag 01PW that the repository does not have.

## What is not done, and no tag is attached

Neither label of [Stacks, Tag 0892] is closed here and no attribute is attached. Part (1) stands
on `Stacks.AmplePullbackPart1.EventualAffineDatum`, which the statement of Tag 0892 does not have as a
hypothesis, so the label is not attached. Two further pieces of bookkeeping are
owed before the argument above can be written down even granted Tag 01PW: the nonvanishing open
of a section over an open subscheme and its compatibility with restriction along the open
immersion, and the `m`-th power of such a section. The *global* analogues are available
(`Stacks.SectionProduct.nonvanishingOpen_mul`,
`Stacks.NonvanishingPullback.preimage_nonvanishingLocus`).

The comparison `Γ((modulePullback U.ι.toLRSHom.toShHom).obj G, ⊤) ≅ Γ(G, U)` that
`StacksFrontier/AlgebraicGeometry/AmpleQuasiAffinePullback/Basic.lean` lists as its third missing
ingredient is proved: `Stacks.AmplePullbackPart1.restrictGlobalSectionsIso`
and `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` in the sibling file
`Restriction.lean`. It is a composition of three facts from the library, two of them `rfl`.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory
open Stacks.NonvanishingOpen (nonvanishingOpen coe_nonvanishingOpen)

universe u

namespace Stacks.AmplePullbackPart1

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Transporting an affine nonvanishing open along an isomorphism of modules -/

section Transport

variable {X : Scheme.{u}}

/-- **The existence of an affine nonvanishing open through a point depends only on the
isomorphism class of the module.** `Stacks.Ample.nonvanishingLocus_congr` transports the locus,
so the two existentials match term by term. This is the only thing the ampleness predicate does
with its module, and it is what makes every comparison isomorphism below usable. -/
theorem exists_affine_nonvanishingOpen_congr {A B : X.Modules} [IsInvertibleModule X A]
    [IsInvertibleModule X B] (e : A ≅ B) (x : X) :
    (∃ s : Γ(A, ⊤), IsAffineOpen (nonvanishingOpen X A s) ∧ x ∈ nonvanishingOpen X A s) ↔
      ∃ s : Γ(B, ⊤), IsAffineOpen (nonvanishingOpen X B s) ∧ x ∈ nonvanishingOpen X B s := by
  have dir : ∀ (A B : X.Modules) (_ : IsInvertibleModule X A) (_ : IsInvertibleModule X B)
      (g : A ≅ B), (∃ s : Γ(A, ⊤), IsAffineOpen (nonvanishingOpen X A s) ∧
          x ∈ nonvanishingOpen X A s) →
        ∃ s : Γ(B, ⊤), IsAffineOpen (nonvanishingOpen X B s) ∧ x ∈ nonvanishingOpen X B s := by
    rintro A B _ _ g ⟨s, haff, hx⟩
    have key : nonvanishingOpen X B (ConcreteCategory.hom (Scheme.Modules.Hom.app g.hom ⊤) s) =
        nonvanishingOpen X A s := Opens.ext (nonvanishingLocus_congr g s)
    exact ⟨_, by rwa [key], by rwa [key]⟩
  exact ⟨dir A B ‹_› ‹_› e, dir B A ‹_› ‹_› e.symm⟩

end Transport

/-! ### The two modules and the isomorphism between their powers -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) (M : S.Modules)
  [IsInvertibleModule X L] [IsInvertibleModule S M]

/-- **`L ⊗ f^* (M ^⊗ a)`, the module part (1) of [Stacks, Tag 0892] concludes about.** The
pullback is `Stacks.AmpleLocallyClosed.pullbackModule`, the tensor product is
`Stacks.RelativeVeryAmple.tensorModules`, and the power of `M` is [Stacks, Tag 01CU]'s. -/
abbrev tensorPullbackPowModule (a : ℕ) : X.Modules :=
  Stacks.RelativeVeryAmple.tensorModules X L
    (Stacks.AmpleLocallyClosed.pullbackModule f (tensorPowModule S M (a : ℤ)))

/-- **`L ^⊗ k ⊗ (f^* M) ^⊗ (a k)`**, the module that the `k`-th tensor power of
`Stacks.AmplePullbackPart1.tensorPullbackPowModule` is isomorphic to, and the module Tag 01PW
produces a section of. -/
abbrev tensorPullbackSplitModule (a k : ℕ) : X.Modules :=
  Stacks.RelativeVeryAmple.tensorModules X (tensorPowModule X L (k : ℤ))
    (tensorPowModule X (Stacks.AmpleLocallyClosed.pullbackModule f M) ((a : ℤ) * (k : ℤ)))

/-- **`(L ⊗ f^* M ^⊗ a) ^⊗ k ≅ L ^⊗ k ⊗ (f^* M) ^⊗ (a k)`.**

Three isomorphisms from the library and one new one:
`Stacks.AmplePullbackPart1.tensorPowModuleTensorIso` distributes the `k`-th power over the tensor
product, `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` moves the `a`-th power across the
pullback, and `Stacks.RelativeVeryAmple.tensorPowModulePowIso` multiplies the two exponents. The
left-hand factor is untouched. -/
def tensorPullbackPowIso (a k : ℕ) :
    tensorPowModule X (tensorPullbackPowModule f L M a) (k : ℤ) ≅
      tensorPullbackSplitModule f L M a k :=
  letI : IsInvertibleModule X
      (tensorPowModule X (Stacks.AmpleLocallyClosed.pullbackModule f M) (a : ℤ)) :=
    isInvertibleModule_tensorPowModule X
      (Stacks.AmpleLocallyClosed.pullbackModule f M) (a : ℤ)
  tensorPowModuleTensorIso X L
      (Stacks.AmpleLocallyClosed.pullbackModule f (tensorPowModule S M (a : ℤ))) k ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl (tensorPowModule X L (k : ℤ)))
      (Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso X _ _
          (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f M a) k ≪≫
        Stacks.RelativeVeryAmple.tensorPowModulePowIso X
          (Stacks.AmpleLocallyClosed.pullbackModule f M) (a : ℤ) k)

/-! ### The target shape -/

/-- **Ampleness of `L ⊗ f^* M ^⊗ a`, in the shape the output of [Stacks, Tag 01PW] is consumed
in.** For a fixed `a` it is exactly quasi-compactness of `X` together with: every point of `X`
lies in an affine nonvanishing open of a global section of `L ^⊗ k ⊗ (f^* M) ^⊗ (a k)` for some
`k ≥ 1`.

`Stacks.AmpleTheory.isAmple_iff_forall_affine_nonvanishingOpen` is the same statement about the
powers of `L ⊗ f^* M ^⊗ a` itself; the content here is that
`Stacks.AmplePullbackPart1.tensorPullbackPowIso` lets the section be produced in the split
module, which is the only module Tag 01PW can speak about. -/
theorem isAmple_tensorPullbackPowModule_iff (a : ℕ) :
    IsAmple X (tensorPullbackPowModule f L M a) ↔ CompactSpace X ∧ ∀ x : X, ∃ k : ℕ, 1 ≤ k ∧
      ∃ s : Γ(tensorPullbackSplitModule f L M a k, ⊤),
        IsAffineOpen (nonvanishingOpen X (tensorPullbackSplitModule f L M a k) s) ∧
          x ∈ nonvanishingOpen X (tensorPullbackSplitModule f L M a k) s := by
  rw [isAmple_iff_forall_affine_nonvanishingOpen]
  exact and_congr_right fun _ => forall_congr' fun x => exists_congr fun k =>
    and_congr_right fun _ => exists_affine_nonvanishingOpen_congr (tensorPullbackPowIso f L M a k) x

/-! ### The pointwise datum, and the uniform threshold -/

/-- **The pointwise datum that part (1) of [Stacks, Tag 0892] is equivalent to.** For every
`x : X` there are a threshold `e` and an *affine* open `V ∋ x`, independent of `a`, such that for
every `a ≥ e` some positive tensor power `L ^⊗ k ⊗ (f^* M) ^⊗ (a k)` carries a global section
whose nonvanishing open is exactly `V`.

That the open does not depend on `a` is what makes the threshold uniform over `X`: the finite
subcover extracted from quasi-compactness has to be chosen once, before `a` is known. It is also
what the intended proof produces — the section for exponent `a` is the one for exponent `e`
multiplied by a power of `f^* t`, which changes the degree and not the nonvanishing locus. -/
def EventualAffineDatum : Prop :=
  ∀ x : X, ∃ (e : ℕ) (V : X.Opens), x ∈ V ∧ IsAffineOpen V ∧
    ∀ a : ℕ, e ≤ a → ∃ k : ℕ, 1 ≤ k ∧
      ∃ s : Γ(tensorPullbackSplitModule f L M a k, ⊤),
        nonvanishingOpen X (tensorPullbackSplitModule f L M a k) s = V

/-- **Part (1) of [Stacks, Tag 0892] from the pointwise datum.** A quasi-compact `X` and
`Stacks.AmplePullbackPart1.EventualAffineDatum` give a single threshold `n` beyond which
`L ⊗ f^* M ^⊗ a` is ample — the `∃ n, ∀ a ≥ n` of the statement of Tag 0892.

Quasi-compactness is used once, to cut the cover `{V x}` down to a finite subfamily; the
threshold is the maximum of the finitely many thresholds that survive. For `a` beyond it every
point of `X` lies in one of the chosen `V`, and the datum supplies a section of the split module
with that exact nonvanishing open, which
`Stacks.AmplePullbackPart1.isAmple_tensorPullbackPowModule_iff` turns into ampleness. -/
theorem exists_threshold_isAmple (hX : CompactSpace X) (h : EventualAffineDatum f L M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a → IsAmple X (tensorPullbackPowModule f L M a) := by
  choose e V hmem haff hsec using h
  obtain ⟨T, hT⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).isOpen) fun y _ => Set.mem_iUnion.mpr ⟨y, hmem y⟩
  refine ⟨T.sup e, fun a ha => (isAmple_tensorPullbackPowModule_iff f L M a).mpr ⟨hX, fun y => ?_⟩⟩
  obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ y))
  obtain ⟨k, hk, s, hs⟩ := hsec x a ((Finset.le_sup hxT).trans ha)
  exact ⟨k, hk, s, by rw [hs]; exact haff x, by rw [hs]; exact hyx⟩

/-! ### Quasi-separatedness, the hypothesis Tag 01PW needs on `X` -/

/-- **A scheme carrying an ample invertible module is quasi-separated.** With quasi-compactness,
which ampleness also gives, this is the whole hypothesis of [Stacks, Tag 01PW] on the scheme.

`StacksFrontier/AlgebraicGeometry/AmpleQuasiAffinePullback/Basic.lean` lists this as the fourth of
the four ingredients missing for part (1), on the ground that `QuasiSeparatedSpace.of_isTopologicalBasis`
asks for a
*basis* of opens with quasi-compact pairwise intersections and "that the affine `X_s` form a basis
is clause (4) of Stacks Tag 01Q3, also unproved here". **Clause (4) is proved, with no premise**,
by `Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple`
(`../SectionExtension/AmpleConsumers.lean:119`), and this lemma is its
three-line consequence. The pairwise intersections are affine by [Stacks, Tag 01PV],
`Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`, hence quasi-compact. -/
theorem quasiSeparatedSpace_of_isAmple {Y : Scheme.{u}} (N : Y.Modules) [IsInvertibleModule Y N]
    (hN : IsAmple Y N) : QuasiSeparatedSpace Y := by
  have hb : TopologicalSpace.IsTopologicalBasis
      (((↑) : Y.Opens → Set Y) '' affineNonvanishingOpens Y N) :=
    (isBasis_affineNonvanishingOpens_iff Y N).mpr
      (Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple Y N hN)
  rw [Set.image_eq_range] at hb
  refine QuasiSeparatedSpace.of_isTopologicalBasis hb ?_
  rintro ⟨-, n, -, s, haffs, rfl⟩ ⟨-, m, -, t, -, rfl⟩
  have h := (Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (tensorPowModule Y N (m : ℤ)) t haffs).isCompact
  rwa [Opens.coe_inf] at h

/-! ### The geometric input, unconditionally -/

/-- **A scheme carrying a relatively ample module over a base with an ample module is
quasi-compact.** Relative ampleness includes quasi-compactness of `f`
(`Stacks.RelativeAmple.IsRelativelyAmple.quasiCompact`) and ampleness of `M` makes `S` compact,
so `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` applies. This is the
quasi-compactness hypothesis of `Stacks.AmplePullbackPart1.exists_threshold_isAmple`, available
from the hypotheses of Tag 0892 with nothing added. -/
theorem compactSpace_of_isAmple (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : IsAmple S M) : CompactSpace X :=
  have : CompactSpace S := Stacks.Ample.IsAmple.compactSpace S M hM
  have : QuasiCompact f := hL.quasiCompact
  QuasiCompact.compactSpace_of_compactSpace f

/-- **The geometric input of part (1), with no premise.** For every `x : X` there are `m ≥ 1` and
a global section `t` of `M ^⊗ m` such that

* `S_t` is affine and contains `f x`;
* the nonvanishing open of the pulled-back section `f^* t` of `(f^* M) ^⊗ m` is `f⁻¹(S_t)`; and
* `L` restricted to the open subscheme `f⁻¹(S_t)` is ample.

These are precisely the hypotheses that [Stacks, Tag 01PW] is applied under in the proof of
part (1), with `N = f^* M` and `σ = f^* t`: the first two say that `X_σ = f⁻¹(S_t)`, and the
third is what produces the section of a power of `L` over `X_σ` that Tag 01PW extends.

The three ingredients are `Stacks.Ample.IsAmple.exists_affine_nonvanishingOpen` for `M`,
[Stacks, Tag 0H78] in the form `Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection`, and
the defining clause of [Stacks, Tag 01VH],
`Stacks.RelativeAmple.IsRelativelyAmple.isAmple_preimage`.
-/
theorem exists_isAmple_preimage_of_isRelativelyAmple
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (hM : IsAmple S M) (x : X) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ t : Γ(tensorPowModule S M (m : ℤ), ⊤),
      IsAffineOpen (powNonvanishingOpen S M m t) ∧
        f.base x ∈ powNonvanishingOpen S M m t ∧
        powNonvanishingOpen X (Stacks.AmpleLocallyClosed.pullbackModule f M) m
            (Stacks.NonvanishingPullback.pullbackPowSection f M m t) =
          f ⁻¹ᵁ powNonvanishingOpen S M m t ∧
        IsAmple (f ⁻¹ᵁ powNonvanishingOpen S M m t).toScheme
          ((modulePullback (f ⁻¹ᵁ powNonvanishingOpen S M m t).ι.toLRSHom.toShHom).obj L) := by
  obtain ⟨m, hm, t, haff, hfx⟩ := IsAmple.exists_affine_nonvanishingOpen S M hM (f.base x)
  exact ⟨m, hm, t, haff, hfx,
    Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection f M m t,
    hL.2 _ haff⟩

end Stacks.AmplePullbackPart1

end
