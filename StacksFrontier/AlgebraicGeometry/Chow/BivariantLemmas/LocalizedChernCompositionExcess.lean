module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.AssociativityOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalSubbundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernComposition
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClassGenuine
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantClassCopy

/-!
# Stacks 0FEC: splitting off the excess normal sheaf

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Z ⊆ Y ⊆ X` be closed
immersions `i : Z ⟶ Y`, `j : Y ⟶ X` of schemes locally of finite type over `S`, and let
`𝒩, 𝒩', 𝒩''` be virtual normal sheaves for `Z ⊆ X`, `Z ⊆ Y`, `Y ⊆ X` with a short exact top row
`(𝒩'')^∨|_Z ⟶ 𝒩^∨ ⟶ (𝒩')^∨` compatible with the conormal sequence: the datum
`Stacks.Chow.ConormalCompatibleVirtualNormalBundles` of Stacks 0FEC. Suppose `j` is a regular
immersion, so that `𝒞_{Y/X}` is finite locally free. The proof of Stacks 0FEC then reduces to
`𝒩'' = 𝒞_{Y/X}^∨`, as follows.

Let `σ'' : (𝒩'')^∨ ⟶ 𝒞_{Y/X}` be the surjection of `𝒩''` and `ℰ = (ker σ'')^∨` its excess normal
sheaf, so that `0 ⟶ ℰ^∨ ⟶ (𝒩'')^∨ ⟶ 𝒞_{Y/X} ⟶ 0` is short exact. Then `𝒩 ⟶ i^*ℰ`, the dual of
`i^*(ker σ'') ⟶ (𝒩'')^∨|_Z ⟶ 𝒩^∨`, is a surjection, its kernel `𝒩₁` is finite locally free,
and the surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors through `𝒩₁^∨`, so that `𝒩₁` is a virtual normal
sheaf for `Z ⊆ X` and `0 ⟶ 𝒩₁ ⟶ 𝒩 ⟶ i^*ℰ ⟶ 0` satisfies the hypotheses of Stacks 0FBL. The
triple `𝒩₁, 𝒩', 𝒞_{Y/X}^∨` is again a datum of Stacks 0FEC: its top row is
`0 ⟶ i^*𝒞_{Y/X} ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨ ⟶ 0`, the sequence of quotients `𝒜/𝒦 ⟶ ℬ/𝒦 ⟶ ℬ/𝒜` for
`𝒦 = i^*(ker σ'') ⊆ 𝒜 = (𝒩'')^∨|_Z ⊆ ℬ = 𝒩^∨`. By Stacks 0FBL

  `c(Y ⟶ X, 𝒩'') = c_top(ℰ) ∘ c(Y ⟶ X, 𝒞_{Y/X}^∨)`  and
  `c(Z ⟶ X, 𝒩) = c_top(i^*ℰ) ∘ c(Z ⟶ X, 𝒩₁)`,

and since Chern classes commute with bivariant classes (Stacks 02UA (2)) it suffices to prove
`c(Z ⟶ X, 𝒩₁) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒞_{Y/X}^∨)`.

## Main definitions

In the namespace `Stacks.Chow.ConormalCompatibleVirtualNormalBundles`:

* `excessMap` — the surjection `𝒩 ⟶ i^*ℰ`.
* `excessKernelBundle` — the virtual normal sheaf `𝒩₁ = ker(𝒩 ⟶ i^*ℰ)` for `Z ⊆ X`.
* `excessReduction` — the reduced datum `𝒩₁, 𝒩', 𝒞_{Y/X}^∨`.

## Main results

* `CategoryTheory.ShortComplex.shortExact_of_quotients` — the third isomorphism theorem in an
  abelian category, as the short exact sequence `0 ⟶ 𝒜/𝒦 ⟶ ℬ/𝒦 ⟶ ℬ/𝒜 ⟶ 0`.
* `Stacks.Chow.VirtualNormalBundle.rank_conormalModule_le` — on a nonempty scheme the rank of
  the conormal sheaf is at most that of a virtual normal sheaf.

In the namespace `Stacks.Chow.ConormalCompatibleVirtualNormalBundles`:

* `isFiniteLocallyFreeOfRank_bundleZX` — `𝒩` has rank `p + q` when `𝒩'` and `𝒩''` have ranks
  `p` and `q`.
* `shortExact_excessMap` and `dualMap_kernel_ι_comp_excessKernelBundle_surjection` — the
  hypotheses of Stacks 0FBL for `0 ⟶ 𝒩₁ ⟶ 𝒩 ⟶ i^*ℰ ⟶ 0`.
* `shortExact_excessReductionDualLeft_excessRight` — the top row of the reduced datum is short
  exact.
* `isFiniteLocallyFreeOfRank_excessKernelBundle` — `𝒩₁` has rank `p + r` when `𝒩'` and
  `𝒞_{Y/X}` have ranks `p` and `r`.
* `excessChernComposite_heq` — `c_top(i^*ℰ) ∘ c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒞_{Y/X}^∨)` is
  `c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`.
* `virtualNormalGysinClass_cap_heq_of_excessReduction` — **the reduction of Stacks 0FEC to
  `𝒩'' = 𝒞_{Y/X}^∨`, on a test scheme**: the identity for `𝒩₁` on a cycle `α` implies the
  identity for `𝒩` on `α`.
* `virtualNormalGysinClass_eq_of_excessReduction` — the same reduction for the classes.

## Implementation notes

The source makes this reduction for `Y ⊆ X` an effective Cartier divisor, after blowing up;
nothing about divisors is used, and it is stated for any regular immersion `j`. It covers in
particular `j` an isomorphism, for which `𝒞_{Y/X} = 0`, `ℰ = (𝒩'')^∨∨` and `𝒩₁` is
`ker(𝒩 ⟶ i^*𝒩'')`.

The classes are those of constant ranks, `p`, `q`, `r` for `𝒩'`, `𝒩''`, `𝒞_{Y/X}`; then `ℰ` has
rank `q - r` and `𝒩₁` rank `p + r`. The truncated difference `q - r` is harmless: on a nonempty
`Y` the surjection `σ''` forces `r ≤ q`, and if `r > q` then `Y` and `Z` are empty and both sides
of every identity vanish.

The excess quotient is taken to be `i^*ℰ` itself, so that the Chern class in Stacks 0FBL on `Z`
is literally the pullback of the one on `Y` that Stacks 02UA (2) moves; the dual of
`i^*(ker σ'') ⟶ 𝒩^∨` lands in `(i^*(ker σ''))^∨`, and the dual base-change isomorphism of
Stacks 0GMX identifies the two. The pullback of `ker σ'' ⟶ (𝒩'')^∨` stays a monomorphism
because its cokernel `𝒞_{Y/X}` is finite locally free.

The field `dualLeft` of `Stacks.Chow.ConormalCompatibleVirtualNormalBundles` has its source
written with `RingedSpaceModuleAdjunction.modulePullback`, which is definitionally, but not
syntactically, `AlgebraicGeometry.Scheme.Modules.pullback`; rewriting a composite of it with a
morphism of `𝒪_Z`-modules fails on the mismatch.
`Stacks.Chow.ConormalCompatibleVirtualNormalBundles.dualLeftHom` is the same morphism with its
source written the second way, and the squares and the top row are restated through it.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 063N](https://stacks.math.columbia.edu/tag/063N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.Immersion Stacks.Thickenings
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

/-! ### A short exact sequence of quotients -/

namespace CategoryTheory.ShortComplex

variable {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] {K A Q₁ B P Q : 𝒞}

/-- **The third isomorphism theorem as a short exact sequence.** Let `K ⟶ A ⟶ B` be
monomorphisms, `v : A ⟶ Q₁` a cokernel of `u : K ⟶ A`, `b : B ⟶ P` a cokernel of `a : A ⟶ B`
and `p : B ⟶ Q` a cokernel of `u ≫ a`. Then the induced maps `l : A/K ⟶ B/K` and
`m : B/K ⟶ B/A` form a short exact sequence `0 ⟶ A/K ⟶ B/K ⟶ B/A ⟶ 0`. The exactness
hypotheses are stated as the minimal ones the chase uses. -/
theorem shortExact_of_quotients {u : K ⟶ A} {v : A ⟶ Q₁} {a : A ⟶ B} {b : B ⟶ P}
    {p : B ⟶ Q} {l : Q₁ ⟶ Q} {m : Q ⟶ P} [Epi v] [Mono a] [Epi b] [Epi p]
    (huv : u ≫ v = 0) (hab : a ≫ b = 0) (hexab : (ShortComplex.mk a b hab).Exact)
    (hp : (u ≫ a) ≫ p = 0) (hexp : (ShortComplex.mk (u ≫ a) p hp).Exact)
    (hl : v ≫ l = a ≫ p) (hm : p ≫ m = b) (hlm : l ≫ m = 0) :
    (ShortComplex.mk l m hlm).ShortExact := by
  have hmono : Mono l := by
    refine Preadditive.mono_of_cancel_zero _ fun {T} x hx ↦ ?_
    obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi v x
    have hy' : (y ≫ a) ≫ p = 0 := by
      rw [Category.assoc, ← hl, ← Category.assoc, ← hy, Category.assoc, hx, Limits.comp_zero]
    obtain ⟨T₂, π₂, _, z, hz⟩ := hexp.exact_up_to_refinements (y ≫ a) hy'
    have hz' : π₂ ≫ y = z ≫ u := by
      rw [← cancel_mono a]
      simpa only [Category.assoc] using hz
    have h0 : (π₂ ≫ π₁) ≫ x = 0 := by
      rw [Category.assoc, hy, ← Category.assoc, hz', Category.assoc, huv, Limits.comp_zero]
    exact (cancel_epi (π₂ ≫ π₁)).1 (h0.trans Limits.comp_zero.symm)
  refine ShortExact.mk' ?_ hmono (epi_of_epi_fac hm)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₂ hx₂
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi p x₂
  have hy' : y ≫ b = 0 := by
    rw [← hm, ← Category.assoc, ← hy, Category.assoc]
    exact (congrArg (π₁ ≫ ·) hx₂).trans Limits.comp_zero
  obtain ⟨T₂, π₂, _, z, hz⟩ := hexab.exact_up_to_refinements y hy'
  refine ⟨T₂, π₂ ≫ π₁, epi_comp _ _, z ≫ v, ?_⟩
  show (π₂ ≫ π₁) ≫ x₂ = (z ≫ v) ≫ l
  rw [Category.assoc, hy, ← Category.assoc, hz, Category.assoc, Category.assoc, hl]

end CategoryTheory.ShortComplex

namespace Stacks.Chow

/-! ### The rank of a virtual normal sheaf bounds that of the conormal sheaf -/

/-- On a nonempty scheme the rank `r` of the conormal sheaf of an immersion is at most the rank
`q` of a virtual normal sheaf for it: the surjection `𝒩^∨ ⟶ 𝒞_{Y/X}` has a kernel of rank
`q - r` and the ranks add up at a point. -/
theorem VirtualNormalBundle.rank_conormalModule_le {Y X : Scheme.{u}} {j : Y ⟶ X} [IsImmersion j]
    (N : VirtualNormalBundle j) (q r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle q]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) r]
    (y : Y) : r ≤ q := by
  let S := ShortComplex.mk (kernel.ι N.conormalSurjection) N.conormalSurjection
    (kernel.condition _)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ (q - r) :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
      N.conormalSurjection inferInstance q r inferInstance inferInstance
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ q :=
    isFiniteLocallyFreeOfRank_dualSheaf N.bundle q inferInstance
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (conormalModule j) r)
  have h := AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact S
    N.shortExact_kernel_surjection (q - r) q r y
  omega

/-! ### Two transports of cycles -/

/-- The operation of a Chow cohomology class on two heterogeneously equal cycles, of equal
degrees, agree up to heterogeneous equality. -/
theorem BivariantClass.idRule_heq_of_heq {C : ChowSituation.{u}} {G : GysinSystem C}
    {W : Scheme.{u}} {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {d : ℤ}
    (x : BivariantClass C G sW sW (𝟙 W) (Category.id_comp sW) d) {T : Scheme.{u}} (t : T ⟶ W)
    [LocallyOfFiniteType t] {m m' : ℤ} (hm : m = m') {β : chowGroup C (t ≫ sW) m}
    {β' : chowGroup C (t ≫ sW) m'} (h : β ≍ β') :
    x.idRule C sW G t m β ≍ x.idRule C sW G t m' β' := by
  subst hm
  obtain rfl := eq_of_heq h
  rfl

/-- Two cycles on an empty scheme, of equal degrees, are heterogeneously equal: the Chow groups
of an empty scheme vanish. -/
theorem chowGroup_heq_of_isEmpty (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] [IsEmpty P] {m m' : ℤ} (hm : m = m') (x : chowGroup C sP m)
    (y : chowGroup C sP m') : x ≍ y := by
  subst hm
  have := subsingleton_chowGroup_of_isEmpty C sP m
  exact heq_of_eq (Subsingleton.elim x y)

namespace ConormalCompatibleVirtualNormalBundles

section Construction

variable {Z Y X : Scheme.{u}} {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
  (D : ConormalCompatibleVirtualNormalBundles i j)

/-! ### The top row -/

/-- The left-hand map `(𝒩'')^∨|_Z ⟶ 𝒩^∨` of the top row, read as a morphism of modules on `Z`
whose source is spelled `AlgebraicGeometry.Scheme.Modules.pullback`. -/
def dualLeftHom : (Scheme.Modules.pullback i).obj (dualSheaf D.bundleYX.bundle) ⟶
    dualSheaf D.bundleZX.bundle :=
  D.dualLeft

/-- The left-hand square, read through
`Stacks.Chow.ConormalCompatibleVirtualNormalBundles.dualLeftHom` and the conormal surjections. -/
theorem dualLeftHom_comp_conormalSurjection :
    D.dualLeftHom ≫ D.bundleZX.conormalSurjection =
      (Scheme.Modules.pullback i).map D.bundleYX.conormalSurjection ≫
        immersionConormalSheafMap (i ≫ j) j i (𝟙 X) (toShHom_square (by simp)) :=
  D.leftSquare

/-- The right-hand square, read through the conormal surjections. -/
theorem dualRight_comp_conormalSurjection :
    D.dualRight ≫ D.bundleZY.conormalSurjection =
      D.bundleZX.conormalSurjection ≫ conormalSequenceRightMap i j :=
  D.rightSquare

/-- The top row `(𝒩'')^∨|_Z ⟶ 𝒩^∨ ⟶ (𝒩')^∨` is a complex. -/
theorem dualLeftHom_comp_dualRight : D.dualLeftHom ≫ D.dualRight = 0 :=
  D.shortExact.choose

/-- The top row `0 ⟶ (𝒩'')^∨|_Z ⟶ 𝒩^∨ ⟶ (𝒩')^∨ ⟶ 0` is short exact. -/
theorem shortExact_dualLeftHom_dualRight :
    (ShortComplex.mk _ _ D.dualLeftHom_comp_dualRight).ShortExact :=
  D.shortExact.choose_spec

/-- **The rank of `𝒩` is the sum of the ranks of `𝒩'` and `𝒩''`.** -/
instance isFiniteLocallyFreeOfRank_bundleZX (p q : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZX.bundle
      (p + q) := by
  have h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj (dualSheaf D.bundleYX.bundle)) q :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i _ q
  have h₂ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _
    D.shortExact_dualLeftHom_dualRight q p h₁ inferInstance
  have := Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_isIso_of_isFiniteLocallyFree
    D.bundleZX.bundle D.bundleZX.isFiniteLocallyFree
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf (dualSheaf D.bundleZX.bundle)) (p + q) := by
    rw [Nat.add_comm]
    exact @isFiniteLocallyFreeOfRank_dualSheaf _ _ _ h₂
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (asIso (toDoubleDual D.bundleZX.bundle)).symm inferInstance

/-! ### The excess quotient of `𝒩` -/

/-- The kernel `ker σ''` of the surjection `σ'' : (𝒩'')^∨ ⟶ 𝒞_{Y/X}`, whose dual is the excess
normal sheaf `ℰ` of `𝒩''`. -/
abbrev excessKernel : Y.Modules :=
  kernel D.bundleYX.conormalSurjection

/-- The map `i^*(ker σ'') ⟶ i^*((𝒩'')^∨) ⟶ 𝒩^∨`, whose dual is the surjection `𝒩 ⟶ i^*ℰ`. -/
def excessDualMap : (Scheme.Modules.pullback i).obj D.excessKernel ⟶
    dualSheaf D.bundleZX.bundle :=
  (Scheme.Modules.pullback i).map (kernel.ι D.bundleYX.conormalSurjection) ≫ D.dualLeftHom

variable (hj : IsRegularImmersion j)
include hj

/-- `ker σ''` is finite locally free: `σ''` is an epimorphism of finite locally free modules, the
conormal sheaf of a regular immersion being finite locally free (Stacks 063N). -/
theorem isFiniteLocallyFree_excessKernel :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} D.excessKernel :=
  D.bundleYX.isFiniteLocallyFree_kernel_surjection (isFiniteLocallyFree_conormalModule j hj)

/-- The pulled-back kernel sequence `0 ⟶ i^*(ker σ'') ⟶ i^*((𝒩'')^∨) ⟶ i^*𝒞_{Y/X} ⟶ 0` is
short exact: its quotient `𝒞_{Y/X}` is finite locally free. -/
theorem shortExact_pullback_kernelSequence :
    ((ShortComplex.mk (kernel.ι D.bundleYX.conormalSurjection) D.bundleYX.conormalSurjection
      (kernel.condition _)).map (Scheme.Modules.pullback i)).ShortExact := by
  have := isFiniteLocallyFree_conormalModule j hj
  exact Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree i _
    D.bundleYX.shortExact_kernel_surjection

/-- The pulled-back surjection `i^*(𝒩'')^∨ ⟶ i^*𝒞_{Y/X}` is an epimorphism. -/
private theorem epi_pullback_map_conormalSurjection :
    Epi ((Scheme.Modules.pullback i).map D.bundleYX.conormalSurjection) :=
  (D.shortExact_pullback_kernelSequence hj).epi_g

/-- The dual base-change isomorphism `i^*ℰ = i^*((ker σ'')^∨) ≅ (i^*(ker σ''))^∨`. -/
def excessPullbackDualIso :
    (Scheme.Modules.pullback i).obj D.bundleYX.excessNormalSheaf ≅
      dualSheaf ((Scheme.Modules.pullback i).obj D.excessKernel) :=
  @asIso _ _ _ _ (pullbackDualMap i D.excessKernel)
    (pullbackDualMap_isIso i _ (D.isFiniteLocallyFree_excessKernel hj))

/-- **The surjection `𝒩 ⟶ i^*ℰ`**: the reflexivity isomorphism `𝒩 ≅ 𝒩^∨∨`, the dual of
`i^*(ker σ'') ⟶ 𝒩^∨` and the dual base-change isomorphism. -/
def excessMap : D.bundleZX.bundle ⟶ (Scheme.Modules.pullback i).obj D.bundleYX.excessNormalSheaf :=
  toDoubleDual D.bundleZX.bundle ≫ dualMap D.excessDualMap ≫ (D.excessPullbackDualIso hj).inv

/-- The dual of `𝒩 ⟶ i^*ℰ`, read on `i^*(ker σ'')` through reflexivity and the dual base-change
isomorphism, is `i^*(ker σ'') ⟶ 𝒩^∨`. -/
theorem toDoubleDual_comp_dualMap_excessMap :
    toDoubleDual _ ≫ dualMap (D.excessPullbackDualIso hj).hom ≫ dualMap (D.excessMap hj) =
      D.excessDualMap := by
  have h1 := toDoubleDual_naturality D.excessDualMap
  have h2 := toDoubleDual_dualMap_comp D.bundleZX.bundle
  have h3 : dualMap (D.excessPullbackDualIso hj).hom ≫
      dualMap (D.excessPullbackDualIso hj).inv = 𝟙 _ := by
    rw [← dualMap_comp, Iso.inv_hom_id, dualMap_id]
  rw [excessMap, dualMap_comp, dualMap_comp, Category.assoc, reassoc_of% h3,
    ← doubleDualMap.eq_def, ← reassoc_of% h1, h2, Category.comp_id]

/-- The isomorphism `i^*(ker σ'') ≅ (i^*ℰ)^∨` through which `i^*(ker σ'') ⟶ 𝒩^∨` is the dual of
`𝒩 ⟶ i^*ℰ`. -/
def excessDualIso :
    (Scheme.Modules.pullback i).obj D.excessKernel ≅
      dualSheaf ((Scheme.Modules.pullback i).obj D.bundleYX.excessNormalSheaf) :=
  haveI := Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_isIso_of_isFiniteLocallyFree
    ((Scheme.Modules.pullback i).obj D.excessKernel)
    (isFiniteLocallyFree_pullback i _ (D.isFiniteLocallyFree_excessKernel hj))
  asIso (toDoubleDual _) ≪≫
    (dualFunctor Z).mapIso (D.excessPullbackDualIso hj).op

/-- `i^*(ker σ'') ⟶ 𝒩^∨` is the dual of `𝒩 ⟶ i^*ℰ`, through
`Stacks.Chow.ConormalCompatibleVirtualNormalBundles.excessDualIso`. -/
theorem excessDualIso_hom_comp_dualMap_excessMap :
    (D.excessDualIso hj).hom ≫ dualMap (D.excessMap hj) = D.excessDualMap :=
  (Category.assoc _ _ _).trans (D.toDoubleDual_comp_dualMap_excessMap hj)

/-- `i^*ℰ` is finite locally free. -/
theorem isFiniteLocallyFree_pullback_excessNormalSheaf :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback i).obj D.bundleYX.excessNormalSheaf) :=
  isFiniteLocallyFree_pullback i _
    (D.bundleYX.isFiniteLocallyFree_excessNormalSheaf (isFiniteLocallyFree_conormalModule j hj))

/-- **`𝒩 ⟶ i^*ℰ` is an epimorphism.** It is the dual of the composite of the two monomorphisms
`i^*(ker σ'') ⟶ i^*((𝒩'')^∨) ⟶ 𝒩^∨`, each the first map of a short exact sequence of finite
locally free modules, so each dualizes to an epimorphism (Stacks 0FV8). -/
theorem epi_excessMap : Epi (D.excessMap hj) := by
  have hpb := D.shortExact_pullback_kernelSequence hj
  have htop := D.shortExact_dualLeftHom_dualRight
  have hK := isFiniteLocallyFree_pullback i _ (D.isFiniteLocallyFree_excessKernel hj)
  have hA := isFiniteLocallyFree_pullback i _ D.bundleYX.isFiniteLocallyFree_dualSheaf
  have hC := isFiniteLocallyFree_pullback i _ (isFiniteLocallyFree_conormalModule j hj)
  obtain ⟨_, h₁⟩ := exists_dualSheaf_shortExact _ _ _ htop.mono_f htop.epi_g htop.exact
    hA
    D.bundleZX.isFiniteLocallyFree_dualSheaf
    D.bundleZY.isFiniteLocallyFree_dualSheaf
  obtain ⟨_, h₂⟩ := exists_dualSheaf_shortExact _ _ _ hpb.mono_f hpb.epi_g hpb.exact
    hK
    hA
    hC
  have := Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_isIso_of_isFiniteLocallyFree
    D.bundleZX.bundle D.bundleZX.isFiniteLocallyFree
  have : Epi (dualMap D.excessDualMap) := by
    rw [excessDualMap, dualMap_comp]
    exact epi_comp' h₁.epi_g h₂.epi_g
  rw [excessMap]
  infer_instance

/-- `𝒩₁ = ker(𝒩 ⟶ i^*ℰ)` is finite locally free: the kernel of an epimorphism of finite locally
free modules. -/
theorem isFiniteLocallyFree_kernel_excessMap :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (kernel (D.excessMap hj)) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi _ (D.epi_excessMap hj)
    D.bundleZX.isFiniteLocallyFree (D.isFiniteLocallyFree_pullback_excessNormalSheaf hj)

/-- **The sequence `0 ⟶ 𝒩₁ ⟶ 𝒩 ⟶ i^*ℰ ⟶ 0` is short exact**, `𝒩₁` being the kernel. -/
theorem shortExact_excessMap :
    (ShortComplex.mk (kernel.ι (D.excessMap hj)) (D.excessMap hj)
      (kernel.condition _)).ShortExact :=
  have := D.epi_excessMap hj
  { exact := ShortComplex.exact_kernel _ }

/-- The dual sequence `(i^*ℰ)^∨ ⟶ 𝒩^∨ ⟶ 𝒩₁^∨` is a complex. -/
theorem dualMap_excessMap_comp_dualMap_kernel_ι :
    dualMap (D.excessMap hj) ≫ dualMap (kernel.ι (D.excessMap hj)) = 0 := by
  rw [← dualMap_comp, kernel.condition, dualMap_zero]

/-- The dual sequence `0 ⟶ (i^*ℰ)^∨ ⟶ 𝒩^∨ ⟶ 𝒩₁^∨ ⟶ 0` is short exact (Stacks 0FV8). -/
theorem shortExact_dualMap_excessMap :
    (ShortComplex.mk (dualMap (D.excessMap hj)) (dualMap (kernel.ι (D.excessMap hj)))
      (D.dualMap_excessMap_comp_dualMap_kernel_ι hj)).ShortExact :=
  have := D.epi_excessMap hj
  (exists_dualSheaf_shortExact _ _ _ inferInstance inferInstance
    (ShortComplex.exact_kernel (D.excessMap hj))
    (D.isFiniteLocallyFree_kernel_excessMap hj)
    D.bundleZX.isFiniteLocallyFree
    (D.isFiniteLocallyFree_pullback_excessNormalSheaf hj)).choose_spec

/-- `i^*(ker σ'') ⟶ 𝒩^∨ ⟶ 𝒩₁^∨` vanishes. -/
theorem excessDualMap_comp_dualMap_kernel_ι :
    D.excessDualMap ≫ dualMap (kernel.ι (D.excessMap hj)) = 0 := by
  rw [← D.excessDualIso_hom_comp_dualMap_excessMap hj, Category.assoc,
    D.dualMap_excessMap_comp_dualMap_kernel_ι hj, Limits.comp_zero]

/-- The sequence `i^*(ker σ'') ⟶ 𝒩^∨ ⟶ 𝒩₁^∨` is exact: it is the dual sequence read through the
isomorphism `i^*(ker σ'') ≅ (i^*ℰ)^∨`. -/
theorem exact_excessDualMap :
    (ShortComplex.mk D.excessDualMap (dualMap (kernel.ι (D.excessMap hj)))
      (D.excessDualMap_comp_dualMap_kernel_ι hj)).Exact :=
  (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (S₁ := ShortComplex.mk _ _ (D.excessDualMap_comp_dualMap_kernel_ι hj))
    (S₂ := ShortComplex.mk _ _ (D.dualMap_excessMap_comp_dualMap_kernel_ι hj))
    (D.excessDualIso hj) (Iso.refl _) (Iso.refl _)
    ((D.excessDualIso_hom_comp_dualMap_excessMap hj).trans (Category.comp_id _).symm)
    (by simp))).2 (D.shortExact_dualMap_excessMap hj).exact

/-- A map out of `𝒩^∨` killing `i^*(ker σ'')` descends to `𝒩₁^∨`, the cokernel of
`(i^*ℰ)^∨ ⟶ 𝒩^∨`. -/
def excessDesc {T : Z.Modules} (g : dualSheaf D.bundleZX.bundle ⟶ T)
    (hg : D.excessDualMap ≫ g = 0) : dualSheaf (kernel (D.excessMap hj)) ⟶ T :=
  (CokernelCofork.IsColimit.desc' (D.shortExact_dualMap_excessMap hj).gIsCokernel g (by
    rw [← cancel_epi (D.excessDualIso hj).hom, ← Category.assoc,
      D.excessDualIso_hom_comp_dualMap_excessMap hj, hg, Limits.comp_zero])).1

/-- `excessDesc g hg` composed with `𝒩^∨ ⟶ 𝒩₁^∨` is `g`. -/
@[reassoc (attr := simp)]
theorem dualMap_kernel_ι_comp_excessDesc {T : Z.Modules} (g : dualSheaf D.bundleZX.bundle ⟶ T)
    (hg : D.excessDualMap ≫ g = 0) :
    dualMap (kernel.ι (D.excessMap hj)) ≫ D.excessDesc hj g hg = g :=
  (CokernelCofork.IsColimit.desc' (D.shortExact_dualMap_excessMap hj).gIsCokernel g _).2

omit hj in
/-- The pulled-back kernel sequence `i^*(ker σ'') ⟶ i^*((𝒩'')^∨) ⟶ i^*𝒞_{Y/X}` is a complex. -/
theorem pullback_map_kernel_ι_comp_conormalSurjection :
    (Scheme.Modules.pullback i).map (kernel.ι D.bundleYX.conormalSurjection) ≫
      (Scheme.Modules.pullback i).map D.bundleYX.conormalSurjection = 0 := by
  rw [← Functor.map_comp, kernel.condition, Functor.map_zero]

omit hj in
/-- `i^*(ker σ'') ⟶ 𝒩^∨` is killed by the surjection `σ` of `𝒩`: by the left-hand square it
factors through `i^*σ''`, which kills `i^*(ker σ'')`. -/
theorem excessDualMap_comp_conormalSurjection :
    D.excessDualMap ≫ D.bundleZX.conormalSurjection = 0 := by
  rw [excessDualMap, Category.assoc, D.dualLeftHom_comp_conormalSurjection]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) D.pullback_map_kernel_ι_comp_conormalSurjection).trans Limits.zero_comp)

omit hj in
/-- `i^*(ker σ'') ⟶ 𝒩^∨` is killed by the right-hand map of the top row. -/
theorem excessDualMap_comp_dualRight : D.excessDualMap ≫ D.dualRight = 0 := by
  rw [excessDualMap, Category.assoc, D.dualLeftHom_comp_dualRight, Limits.comp_zero]

/-! ### The virtual normal sheaf `𝒩₁` -/

/-- **The virtual normal sheaf `𝒩₁` of Stacks 0FEC** for `Z ⊆ X`: the kernel of the surjection
`𝒩 ⟶ i^*ℰ`, with the surjection `𝒩₁^∨ ⟶ 𝒞_{Z/X}` through which `σ` factors. -/
def excessKernelBundle : VirtualNormalBundle (i ≫ j) where
  bundle := kernel (D.excessMap hj)
  isFiniteLocallyFree := D.isFiniteLocallyFree_kernel_excessMap hj
  surjection := D.excessDesc hj D.bundleZX.conormalSurjection
    D.excessDualMap_comp_conormalSurjection
  epi := epi_of_epi_fac (D.dualMap_kernel_ι_comp_excessDesc hj _ _)

/-- The bundle of `𝒩₁` is the kernel of `𝒩 ⟶ i^*ℰ`. -/
@[simp]
theorem excessKernelBundle_bundle :
    (D.excessKernelBundle hj).bundle = kernel (D.excessMap hj) :=
  rfl

/-- **The surjection of `𝒩` factors through that of `𝒩₁`**: `σ = σ₁ ∘ (𝒩^∨ ⟶ 𝒩₁^∨)`. This is
the hypothesis of Stacks 0FBL for `0 ⟶ 𝒩₁ ⟶ 𝒩 ⟶ i^*ℰ ⟶ 0`. -/
theorem dualMap_kernel_ι_comp_excessKernelBundle_surjection :
    dualMap (kernel.ι (D.excessMap hj)) ≫ (D.excessKernelBundle hj).surjection =
      D.bundleZX.surjection :=
  D.dualMap_kernel_ι_comp_excessDesc hj _ D.excessDualMap_comp_conormalSurjection

/-! ### The top row of the reduced datum -/

/-- The map `i^*𝒞_{Y/X} ⟶ 𝒩₁^∨` induced by `(𝒩'')^∨|_Z ⟶ 𝒩^∨ ⟶ 𝒩₁^∨`. -/
def excessLeft : (Scheme.Modules.pullback i).obj (conormalModule j) ⟶
    dualSheaf (kernel (D.excessMap hj)) :=
  (CokernelCofork.IsColimit.desc' (D.shortExact_pullback_kernelSequence hj).gIsCokernel
    (D.dualLeftHom ≫ dualMap (kernel.ι (D.excessMap hj)))
    ((Category.assoc _ _ _).symm.trans (D.excessDualMap_comp_dualMap_kernel_ι hj))).1

/-- `i^*((𝒩'')^∨) ⟶ i^*𝒞_{Y/X} ⟶ 𝒩₁^∨` is `(𝒩'')^∨|_Z ⟶ 𝒩^∨ ⟶ 𝒩₁^∨`. -/
theorem pullback_map_conormalSurjection_comp_excessLeft :
    (Scheme.Modules.pullback i).map D.bundleYX.conormalSurjection ≫ D.excessLeft hj =
      D.dualLeftHom ≫ dualMap (kernel.ι (D.excessMap hj)) :=
  (CokernelCofork.IsColimit.desc' (D.shortExact_pullback_kernelSequence hj).gIsCokernel _ _).2

/-- The map `𝒩₁^∨ ⟶ (𝒩')^∨` induced by `𝒩^∨ ⟶ (𝒩')^∨`. -/
def excessRight : dualSheaf (kernel (D.excessMap hj)) ⟶ dualSheaf D.bundleZY.bundle :=
  D.excessDesc hj D.dualRight D.excessDualMap_comp_dualRight

/-- `𝒩^∨ ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨` is the right-hand map of the top row. -/
theorem dualMap_kernel_ι_comp_excessRight :
    dualMap (kernel.ι (D.excessMap hj)) ≫ D.excessRight hj = D.dualRight :=
  D.dualMap_kernel_ι_comp_excessDesc hj _ _

/-- `i^*𝒞_{Y/X} ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨` is a complex. -/
theorem excessLeft_comp_excessRight : D.excessLeft hj ≫ D.excessRight hj = 0 := by
  rw [← cancel_epi ((Scheme.Modules.pullback i).map D.bundleYX.conormalSurjection),
    ← Category.assoc, D.pullback_map_conormalSurjection_comp_excessLeft hj, Category.assoc,
    D.dualMap_kernel_ι_comp_excessRight hj, Limits.comp_zero]
  exact D.dualLeftHom_comp_dualRight

/-- **`0 ⟶ i^*𝒞_{Y/X} ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨ ⟶ 0` is short exact**: it is the sequence of quotients
`𝒜/𝒦 ⟶ ℬ/𝒦 ⟶ ℬ/𝒜` for `𝒦 = i^*(ker σ'') ⊆ 𝒜 = (𝒩'')^∨|_Z ⊆ ℬ = 𝒩^∨`. -/
theorem shortExact_excessLeft_excessRight :
    (ShortComplex.mk _ _ (D.excessLeft_comp_excessRight hj)).ShortExact := by
  have htop := D.shortExact_dualLeftHom_dualRight
  have := htop.mono_f
  have := htop.epi_g
  have := (D.shortExact_dualMap_excessMap hj).epi_g
  have := D.epi_pullback_map_conormalSurjection hj
  exact ShortComplex.shortExact_of_quotients D.pullback_map_kernel_ι_comp_conormalSurjection
    D.dualLeftHom_comp_dualRight htop.exact
    (D.excessDualMap_comp_dualMap_kernel_ι hj) (D.exact_excessDualMap hj)
    (D.pullback_map_conormalSurjection_comp_excessLeft hj)
    (D.dualMap_kernel_ι_comp_excessRight hj) _

/-- The left-hand square of the reduced datum, before the reflexivity isomorphism of
`𝒞_{Y/X}`: `i^*𝒞_{Y/X} ⟶ 𝒩₁^∨ ⟶ 𝒞_{Z/X}` is the canonical map of Stacks 01R4. -/
theorem excessLeft_comp_surjection :
    D.excessLeft hj ≫ (D.excessKernelBundle hj).surjection =
      immersionConormalSheafMap (i ≫ j) j i (𝟙 X) (toShHom_square (by simp)) := by
  have := D.epi_pullback_map_conormalSurjection hj
  refine (cancel_epi ((Scheme.Modules.pullback i).map D.bundleYX.conormalSurjection)).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (D.excessKernelBundle hj).surjection)
      (D.pullback_map_conormalSurjection_comp_excessLeft hj)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (D.dualLeftHom ≫ ·)
          (D.dualMap_kernel_ι_comp_excessKernelBundle_surjection hj)).trans
          D.dualLeftHom_comp_conormalSurjection)))

/-- The right-hand square of the reduced datum. -/
theorem excessRight_comp_surjection :
    D.excessRight hj ≫ D.bundleZY.surjection =
      (D.excessKernelBundle hj).surjection ≫ conormalSequenceRightMap i j := by
  have := (D.shortExact_dualMap_excessMap hj).epi_g
  refine (cancel_epi (dualMap (kernel.ι (D.excessMap hj)))).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ D.bundleZY.surjection) (D.dualMap_kernel_ι_comp_excessRight hj)).trans
      (D.rightSquare.trans ((congrArg (· ≫ conormalSequenceRightMap i j)
        (D.dualMap_kernel_ι_comp_excessKernelBundle_surjection hj)).symm.trans
          (Category.assoc _ _ _))))

variable [IsLocallyNoetherian Y]

/-- The left-hand map `(𝒞_{Y/X}^∨)^∨|_Z ⟶ 𝒩₁^∨` of the top row of the reduced datum: the
pulled-back reflexivity isomorphism `𝒞_{Y/X}^∨∨ ≅ 𝒞_{Y/X}` followed by `i^*𝒞_{Y/X} ⟶ 𝒩₁^∨`. -/
def excessReductionDualLeft :
    (Scheme.Modules.pullback i).obj (dualSheaf (dualSheaf (conormalModule j))) ⟶
      dualSheaf (kernel (D.excessMap hj)) :=
  (Scheme.Modules.pullback i).map (regularNormalSurjection j hj) ≫ D.excessLeft hj

/-- The top row of the reduced datum is a complex. -/
theorem excessReductionDualLeft_comp_excessRight :
    D.excessReductionDualLeft hj ≫ D.excessRight hj = 0 := by
  rw [excessReductionDualLeft, Category.assoc, D.excessLeft_comp_excessRight hj,
    Limits.comp_zero]

/-- **The top row of the reduced datum is short exact**: up to the reflexivity isomorphism of
`𝒞_{Y/X}` it is `0 ⟶ i^*𝒞_{Y/X} ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨ ⟶ 0`. -/
theorem shortExact_excessReductionDualLeft_excessRight :
    (ShortComplex.mk _ _ (D.excessReductionDualLeft_comp_excessRight hj)).ShortExact := by
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (S₁ := ShortComplex.mk _ _ (D.excessLeft_comp_excessRight hj))
    ((Scheme.Modules.pullback i).mapIso (conormalReflexiveIso j hj)) (Iso.refl _) (Iso.refl _)
    ?_ ?_) (D.shortExact_excessLeft_excessRight hj)
  · show (Scheme.Modules.pullback i).map (toDoubleDual (conormalModule j)) ≫
      (Scheme.Modules.pullback i).map (regularNormalSurjection j hj) ≫ D.excessLeft hj =
        D.excessLeft hj ≫ 𝟙 _
    rw [← Category.assoc, ← Functor.map_comp, toDoubleDual_comp_regularNormalSurjection,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · simp

/-- **The reduced datum of Stacks 0FEC.** From the datum `𝒩, 𝒩', 𝒩''` for `Z ⊆ Y ⊆ X` and a
regular immersion `Y ⊆ X`, the datum `𝒩₁, 𝒩', 𝒞_{Y/X}^∨`: the virtual normal sheaf `𝒩₁` for
`Z ⊆ X` of `Stacks.Chow.ConormalCompatibleVirtualNormalBundles.excessKernelBundle`, the same
`𝒩'` for `Z ⊆ Y`, and the normal bundle of `Y ⊆ X`. -/
def excessReduction : ConormalCompatibleVirtualNormalBundles i j where
  bundleZX := D.excessKernelBundle hj
  bundleZY := D.bundleZY
  bundleYX := VirtualNormalBundle.ofIsRegularImmersion j hj
  dualLeft := D.excessReductionDualLeft hj
  dualRight := D.excessRight hj
  shortExact := ⟨_, D.shortExact_excessReductionDualLeft_excessRight hj⟩
  leftSquare := (Category.assoc _ _ _).trans
    (congrArg ((Scheme.Modules.pullback i).map (regularNormalSurjection j hj) ≫ ·)
      (D.excessLeft_comp_surjection hj))
  rightSquare := D.excessRight_comp_surjection hj

/-- The virtual normal sheaf for `Z ⊆ X` of the reduced datum is `𝒩₁`. -/
@[simp]
theorem excessReduction_bundleZX : (D.excessReduction hj).bundleZX = D.excessKernelBundle hj :=
  rfl

/-- The virtual normal sheaf for `Z ⊆ Y` of the reduced datum is `𝒩'`. -/
@[simp]
theorem excessReduction_bundleZY : (D.excessReduction hj).bundleZY = D.bundleZY :=
  rfl

/-- The virtual normal sheaf for `Y ⊆ X` of the reduced datum is the normal bundle
`𝒞_{Y/X}^∨`. -/
@[simp]
theorem excessReduction_bundleYX :
    (D.excessReduction hj).bundleYX = VirtualNormalBundle.ofIsRegularImmersion j hj :=
  rfl

/-! ### Ranks -/

/-- **`𝒩₁` has rank `p + r`** when `𝒩'` has rank `p` and `𝒞_{Y/X}` has rank `r`: its dual is an
extension of `(𝒩')^∨` by `i^*𝒞_{Y/X}`. -/
instance isFiniteLocallyFreeOfRank_excessKernelBundle (p r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (D.excessKernelBundle hj).bundle (p + r) :=
  @isFiniteLocallyFreeOfRank_bundleZX _ _ _ _ _ _ _ (D.excessReduction hj) p r
    (inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      D.bundleZY.bundle p))
    (VirtualNormalBundle.isFiniteLocallyFreeOfRank_ofIsRegularImmersion_bundle hj r)

/-- The virtual normal sheaf for `Z ⊆ X` of the reduced datum has rank `p + r`. -/
instance isFiniteLocallyFreeOfRank_excessReduction_bundleZX (p r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (D.excessReduction hj).bundleZX.bundle (p + r) :=
  D.isFiniteLocallyFreeOfRank_excessKernelBundle hj p r

omit hj [IsLocallyNoetherian Y] in
/-- **`i^*ℰ` has rank `q - r`** when `𝒩''` has rank `q` and `𝒞_{Y/X}` has rank `r`. -/
instance isFiniteLocallyFreeOfRank_pullback_excessNormalSheaf (q r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj D.bundleYX.excessNormalSheaf) (q - r) :=
  haveI := D.bundleYX.isFiniteLocallyFreeOfRank_excessNormalSheaf q r
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i _ (q - r)

end Construction

/-! ### Stacks 0FEC reduced to the normal bundle of `Y ⊆ X` -/

section Reduction

variable (C : ChowSituation.{u}) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {i : Z ⟶ Y} [IsClosedImmersion i] {j : Y ⟶ X} [IsClosedImmersion j] [IsLocallyNoetherian Y]
  (hi : i ≫ sY = sZ) (hj' : j ≫ sX = sY) (D : ConormalCompatibleVirtualNormalBundles i j)
  (hj : IsRegularImmersion j) (p q r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) r]

include hj in
/-- **Splitting off the excess normal sheaf, as classes.** For `r ≤ q`, with `e = q - r`:

  `c_e(i^*ℰ) ∘ (c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒞_{Y/X}^∨)) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`.

By Stacks 0FBL on `Y`, `c(Y ⟶ X, 𝒩'') = c_e(ℰ) ∘ c(Y ⟶ X, 𝒞_{Y/X}^∨)`; Chern classes commute
with bivariant classes (Stacks 02UA (2)), and composition is associative. -/
theorem excessChernComposite_heq (hrq : r ≤ q) :
    bivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) (i ≫ j) (Category.id_comp sZ)
        (comp_comp_structureMorphism_eq hi hj') ((q - r : ℕ) : ℤ) ((p : ℤ) + (r : ℤ))
        (GenuineChern.chernClass C sZ
          ((Scheme.Modules.pullback i).obj D.bundleYX.excessNormalSheaf) (q - r)
          (Fin.last (q - r)))
        (bivariantCompositeOfInvertible C sZ sY sX i j hi hj' (p : ℤ) (r : ℤ)
          (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
          (virtualNormalBundleClass C sY sX j hj' (VirtualNormalBundle.ofIsRegularImmersion j hj)
            r)) ≍
      bivariantCompositeOfInvertible C sZ sY sX i j hi hj' (p : ℤ) (q : ℤ)
        (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
        (virtualNormalBundleClass C sY sX j hj' D.bundleYX q) := by
  set e := q - r with he
  have hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      D.bundleYX.excessNormalSheaf e := D.bundleYX.isFiniteLocallyFreeOfRank_excessNormalSheaf q r
  have hC := isFiniteLocallyFree_conormalModule j hj
  have hN'' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      D.bundleYX.bundle (r + e) :=
    GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ (D.bundleYX.shortExact_excess hC) r e
      (VirtualNormalBundle.isFiniteLocallyFreeOfRank_ofIsRegularImmersion_bundle hj r) hE
  have h0FBL := virtualNormalBundleClass_eq_of_isTopChernComposition C sY sX j hj' D.bundleYX
    (VirtualNormalBundle.ofIsRegularImmersion j hj) r e D.bundleYX.excessNormalSheaf
    D.bundleYX.excessInclusion D.bundleYX.excessProjection
    D.bundleYX.excessInclusion_comp_excessProjection (D.bundleYX.shortExact_excess hC)
    (D.bundleYX.dualMap_excessInclusion_comp_surjection hj)
  have hY : bivariantCompositeOfInvertible C sY sY sX (𝟙 Y) j (Category.id_comp sY) hj'
        (e : ℤ) (r : ℤ) (GenuineChern.chernClass C sY D.bundleYX.excessNormalSheaf e (Fin.last e))
        (virtualNormalBundleClass C sY sX j hj' (VirtualNormalBundle.ofIsRegularImmersion j hj)
          r) ≍
      virtualNormalBundleClass C sY sX j hj' D.bundleYX q := by
    refine (BivariantClass.copy_heq _ _ _ _ _).symm.trans ((heq_of_eq h0FBL).symm.trans ?_)
    exact virtualNormalGysinClass_heq_of_rank_eq C sY sX j hj' D.bundleYX (by omega)
  refine (bivariantCompositeOfInvertible_assoc C sZ sZ sY sX (𝟙 Z) i j (Category.id_comp sZ) hi
    hj' _ _ _ _ _ _).symm.trans ?_
  refine (bivariantCompositeOfInvertible_heq_congr (by simp) rfl (add_comm _ _) rfl
    (BivariantClass.heq_bivariantCompositeOfInvertible_chernClass
      (virtualNormalBundleClass C sZ sY i hi D.bundleZY p) D.bundleYX.excessNormalSheaf e
      (Fin.last e)).symm HEq.rfl).trans ?_
  refine (bivariantCompositeOfInvertible_assoc C sZ sY sY sX i (𝟙 Y) j hi (Category.id_comp sY)
    hj' _ _ _ _ _ _).trans ?_
  exact bivariantCompositeOfInvertible_heq_congr rfl (Category.id_comp j) rfl
    (by rw [Fin.val_last]; omega) HEq.rfl hY

include hj in
/-- **Stacks 0FEC, the reduction to `𝒩'' = 𝒞_{Y/X}^∨`, on a test scheme.** Let `t : T ⟶ X` be
a test scheme and `α ∈ A_k(T)`. If

  `c(Z ⟶ X, 𝒩₁) ∩ α = c(Z ⟶ Y, 𝒩') ∩ c(Y ⟶ X, 𝒞_{Y/X}^∨) ∩ α`,

then `c(Z ⟶ X, 𝒩) ∩ α = c(Z ⟶ Y, 𝒩') ∩ c(Y ⟶ X, 𝒩'') ∩ α`. The two sides of each identity lie
in Chow groups of degrees which are equal integers written differently, whence the heterogeneous
equalities.

By Stacks 0FBL on `Z`, `c(Z ⟶ X, 𝒩) = c_e(i^*ℰ) ∘ c(Z ⟶ X, 𝒩₁)`, `e = q - r`, so the left-hand
side is `c_e(i^*ℰ) ∩ c(Z ⟶ X, 𝒩₁) ∩ α`, and the hypothesis turns it into the cap product of
`c_e(i^*ℰ) ∘ c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒞_{Y/X}^∨)`, which is
`c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')` (`excessChernComposite_heq`). If `r > q` then `Y`, hence `Z`, is
empty (`Stacks.Chow.VirtualNormalBundle.rank_conormalModule_le`) and both sides vanish. -/
theorem virtualNormalGysinClass_cap_heq_of_excessReduction {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k)
    (h : (virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj')
          (D.excessKernelBundle hj) (p + r)).cap t k α ≍
        (bivariantCompositeOfInvertible C sZ sY sX i j hi hj' (p : ℤ) (r : ℤ)
          (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
          (virtualNormalBundleClass C sY sX j hj' (VirtualNormalBundle.ofIsRegularImmersion j hj)
            r)).cap t k α) :
    (virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj')
        D.bundleZX (p + q)).cap t k α ≍
      (bivariantCompositeOfInvertible C sZ sY sX i j hi hj' (p : ℤ) (q : ℤ)
        (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
        (virtualNormalBundleClass C sY sX j hj' D.bundleYX q)).cap t k α := by
  by_cases hrq : r ≤ q
  · have hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        D.bundleZX.bundle (p + r + (q - r)) :=
      GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ (D.shortExact_excessMap hj)
        (p + r) (q - r) (D.isFiniteLocallyFreeOfRank_excessKernelBundle hj p r) inferInstance
    have h0 := virtualNormalBundleClass_eq_of_isTopChernComposition C sZ sX (i ≫ j)
      (comp_comp_structureMorphism_eq hi hj') D.bundleZX (D.excessKernelBundle hj) (p + r)
      (q - r) ((Scheme.Modules.pullback i).obj D.bundleYX.excessNormalSheaf)
      (kernel.ι (D.excessMap hj)) (D.excessMap hj) (kernel.condition _)
      (D.shortExact_excessMap hj) (D.dualMap_kernel_ι_comp_excessKernelBundle_surjection hj)
    refine (BivariantClass.cap_heq_of_heq rfl (by push_cast; omega)
      (virtualNormalGysinClass_heq_of_rank_eq C sZ sX (i ≫ j) _ D.bundleZX
        (show p + q = p + r + (q - r) by omega)) t k α).trans ?_
    refine (heq_of_eq (congrArg (fun c ↦ c.cap t k α) h0)).trans ?_
    refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans ?_
    refine (BivariantClass.id_bivariantCompositeOfInvertible_cap_heq _ _ t k α).trans ?_
    refine (BivariantClass.idRule_heq_of_heq _ _ (by push_cast; ring) h).trans ?_
    refine (BivariantClass.id_bivariantCompositeOfInvertible_cap_heq _ _ t k α).symm.trans ?_
    exact BivariantClass.cap_heq_of_heq (Category.id_comp _) (by omega)
      (D.excessChernComposite_heq C sZ sY sX hi hj' hj p q r hrq) t k α
  · have : IsEmpty Z := ⟨fun z ↦ hrq (D.bundleYX.rank_conormalModule_le q r (i.base z))⟩
    have : IsEmpty (Limits.pullback (i ≫ j) t : Scheme.{u}) :=
      ⟨fun x ↦ isEmptyElim ((Limits.pullback.fst (i ≫ j) t).base x)⟩
    exact chowGroup_heq_of_isEmpty C _ (by push_cast; ring) _ _

include hj in
/-- **Stacks 0FEC, the reduction to `𝒩'' = 𝒞_{Y/X}^∨`.** For a regular immersion `Y ⊆ X`,
if `c(Z ⟶ X, 𝒩₁) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒞_{Y/X}^∨)` in `A^{p + r}(Z ⟶ X)` then
`c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')` in `A^{p + q}(Z ⟶ X)`, the ranks of `𝒩'`, `𝒩''`
and `𝒞_{Y/X}` being `p`, `q` and `r`. -/
theorem virtualNormalGysinClass_eq_of_excessReduction
    (h : virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj')
        (D.excessKernelBundle hj) (p + r) =
      BivariantClass.copy C (gysinSystemOfInvertible C) sZ sX rfl
        (comp_comp_structureMorphism_eq hi hj') (comp_comp_structureMorphism_eq hi hj')
        (by push_cast; ring)
        (bivariantCompositeOfInvertible C sZ sY sX i j hi hj' (p : ℤ) (r : ℤ)
          (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
          (virtualNormalBundleClass C sY sX j hj' (VirtualNormalBundle.ofIsRegularImmersion j hj)
            r))) :
    virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj') D.bundleZX
        (p + q) =
      BivariantClass.copy C (gysinSystemOfInvertible C) sZ sX rfl
        (comp_comp_structureMorphism_eq hi hj') (comp_comp_structureMorphism_eq hi hj')
        (by push_cast; ring)
        (bivariantCompositeOfInvertible C sZ sY sX i j hi hj' (p : ℤ) (q : ℤ)
          (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
          (virtualNormalBundleClass C sY sX j hj' D.bundleYX q)) := by
  refine BivariantClass.ext C _ sZ sX (i ≫ j) _ _ fun t _ k α ↦ eq_of_heq ?_
  refine HEq.trans ?_ (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).symm
  refine D.virtualNormalGysinClass_cap_heq_of_excessReduction C sZ sY sX hi hj' hj p q r t k α ?_
  exact (heq_of_eq (congrArg (fun c ↦ c.cap t k α) h)).trans
    (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α)

end Reduction

end ConormalCompatibleVirtualNormalBundles

end Stacks.Chow

end
