module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Powers
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Power
public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Powers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Stacks Tag 01PW, the surjectivity half, for an ample invertible module

`StacksFrontier/AlgebraicGeometry/SectionExtension/Basic.lean` isolates the surjectivity half of
Stacks Tag 01PW as `Stacks.SectionExtension.IsSectionRatio` and reduces clauses (3) and (4) of
Stacks Tag 01Q3 and the ample-pullback cluster to it.
`StacksFrontier/AlgebraicGeometry/SectionExtension/GloballyTrivial.lean` proves that predicate
when every tensor power of `L` has a nowhere-vanishing global basis, which is in substance the
quasi-affine case. **This file proves it whenever `L` is ample**, which is the hypothesis every
consumer of the ample cluster holds.

## The argument

`X` is quasi-compact, `s` is a global section of `L ^⊗ n` with `n ≥ 1`, and `g` is a function on
`U = X_s`. The output is a single power `σ = s^{K+1}` of `s` and a global section `t` of the same
tensor power with `t|_U = g · σ|_U`.

1. **One common degree** (`exists_common_degree_affine_cover`). Ampleness covers `X` by affine
   `X_{b}`, one for each point, with `b` homogeneous of some positive degree; quasi-compactness
   cuts that down to finitely many, and
   `Stacks.FinGenFromCover.exists_common_degree_family` together with
   `Stacks.AmpleAffineAvoidance.exists_pow_of_dvd` replaces every member *and* `s` by a power in
   one degree `N`, leaving all the nonvanishing loci unchanged. The whole argument then runs
   inside `Γ(L ^⊗ N, ⊤)`, which is what makes "`s` is `f i` times `c i` on `V i`" a statement at
   all.
2. **The local extension.** On `V i = X_{c i}` the section `c i` is a free generator, so
   `s|_{V i} = f i · c i|_{V i}` for a unique `f i : Γ(X, V i)`
   (`Stacks.NonvanishingSpelling.bijective_smul`), and
   `Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen` — unconditional — identifies
   `U ⊓ V i` with `X.basicOpen (f i)`. Since `V i` is affine,
   `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` writes `g` there as
   `(f i)^{-e i} · c i` for a numerator `c i` over `V i`, and the finitely many exponents are
   raised to a single `k`.
3. **The overlaps.** `V i ⊓ V j` is **affine**, by Stacks Tag 01PV
   (`Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`) applied with the
   affine open `V i` and the section `c j`. So quasi-separatedness of `X` is not used anywhere in
   this file: the Qcqs lemma that `GloballyTrivial.lean` needs is replaced by the affine one.
   Writing `c j|_{V i ⊓ V j} = w i j · c i|_{V i ⊓ V j}`, uniqueness of the ratio gives
   `f i = f j · w i j` there, and from it the two numerators agree on
   `V i ⊓ V j ⊓ U = X.basicOpen (f i|_{V i ⊓ V j})`.
   `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` — the
   injectivity half of Tag 01PW in the only case needed — then kills the difference after
   multiplying by a power of `f i`, and the finitely many exponents are again raised to one,
   `q + 1`.
4. **The gluing.** With `K + 1 = k + (q + 1)` the local sections
   `(f i)^{q+1} · c i ⊗ (c i)^{K+1}|_{V i}` agree on the overlaps, and
   `TopCat.Sheaf.existsUnique_gluing'` on `⟨M.presheaf, M.isSheaf⟩` produces the global `t`. That
   `t|_U = g · s^{K+1}|_U` is then checked on the cover `{U ⊓ V i}` of `U`, by
   `TopCat.Presheaf.IsSheaf.section_ext`.

## What makes step 4 statable

The powers appearing in steps 2 and 4 are the powers of **one global section**, supplied by
`StacksFrontier/AlgebraicGeometry/TensorPowerTrivialize/Power.lean`:
`Stacks.TensorPowerTrivialize.sectionPow` is that power,
`Stacks.TensorPowerTrivialize.resTop_sectionPow` is the identity
`s^{K+1}|_V = f^{K+1} · u^{K+1}|_V`, and
`Stacks.TensorPowerTrivialize.nonvanishingOpen_sectionPow` is `X_{u^{K+1}} = X_u`, which is what
makes `σ` nowhere vanishing on `U`. A trivialization with an *unnamed* local generator — what
clause 2 of Stacks Tag 0B8M hands out — cannot supply the identity of step 4, because the
generators in degree `N` and in degree `N(K+1)` would be unrelated choices.

## Main results

* `Stacks.SectionExtension.exists_common_degree_affine_cover`: the cover, in one degree, and that
  degree is a multiple of the given one.
* `Stacks.SectionExtension.exists_ratio_of_affine_cover`: **the gluing argument**, stated against
  such a cover rather than against ampleness, so that the only use of ampleness in this file is
  producing the cover.
* `Stacks.SectionExtension.isSectionRatio_of_isAmple`: **the deliverable.**
  `Stacks.SectionExtension.IsSectionRatio X L` for `L` ample.
* `Stacks.SectionExtension.nvLocus_powSec_of_one_le`: a by-product. `X_{a^k} = X_a` for `k ≥ 1`
  for the power operation of `StacksFrontier/AlgebraicGeometry/SectionExtension/Powers.lean`,
  with the hypothesis that file carried discharged by `nvLocus_powSec_one`.

## No Stacks attribute is attached

**What is proved is weaker than Stacks Tag 01PW on three counts, each independent.**

1. **`L` is assumed ample.** Tag 01PW assumes only that `X` is quasi-compact (and, for part (2),
   quasi-separated) and that `L` is invertible. Ampleness is used to produce the finite affine
   cover of step 1; nothing weaker is available here, and in particular
   `Stacks.Ample.isQuasiAffine_iff_isAmple` (Tag 01QE) does not help, since it is a statement
   about `Stacks.Ample.unitModule X` alone — a projective scheme carries an ample `L` and is not
   quasi-affine.
2. **Only the surjectivity half is stated.** Tag 01PW asserts that the comparison map
   `Γ_*(X, 𝓕)_{(s)} → Γ(X_s, 𝓕)` is injective for `X` quasi-compact and bijective for `X`
   quasi-compact and quasi-separated. Injectivity is used here only through Mathlib's affine
   statement, and the comparison map itself is not defined in this repository.
3. **Only the case `𝓕 = 𝒪_X`.** Tag 01PW is about an arbitrary quasi-coherent `𝓕`, and the
   conclusion here is an equation between *scalar* multiples. The module-valued form needs a
   tensor product of *sections*, which this repository does not have; see the "What is not done"
   section of `Stacks.SectionExtension.Basic`.

So this is not the covering set of 01PW and carries no attribute. The label stays open, and
`Stacks.SectionExtension.IsSectionRatio` — stated for an arbitrary invertible module on an
arbitrary scheme — stays the open declaration.
`StacksFrontier/AlgebraicGeometry/SectionExtension/AmpleConsumers.lean` records exactly which
consumers the ample case closes and which it does not.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowerTrivialize (sectionPow powDeg)

universe u

namespace Stacks.SectionExtension

/-! ### Ratios of global sections of an invertible module -/

section Ratio

variable {X : Scheme.{u}} (M : X.Modules)

/-- `Stacks.SectionExtension.resTop` and `Stacks.TensorPowerTrivialize.resTop` are the same
restriction, written with their two argument orders. -/
theorem resTop_eq_resTop (U : X.Opens) (t : Γ(M, ⊤)) :
    resTop U t = Stacks.TensorPowerTrivialize.resTop M t U := rfl

/-- **A ratio identity between global sections restricts.** If `t|_V = f • u|_V` then
`t|_W = f|_W • u|_W` for every smaller open `W`. -/
theorem resTop_eq_smul_of_le {u t : Γ(M, ⊤)} {V W : X.Opens} (hWV : W ≤ V) (f : Γ(X, V))
    (h : resTop V t = f • resTop V u) :
    resTop W t = X.presheaf.map (homOfLE hWV).op f • resTop W u := by
  have := congrArg (M.presheaf.map (homOfLE hWV).op) h
  rwa [Stacks.TensorPowerTrivialize.res_resTop, Stacks.TensorPowerTrivialize.map_smul_resTop]
    at this

variable [IsInvertibleModule X M]

/-- **The ratio of two global sections by a nonvanishing one is unique.** Over an open inside
`X_u` the scalar `a` in `a • u|_W` is determined, because multiplication by `u|_W` is injective
there (`Stacks.NonvanishingSpelling.bijective_smul`). -/
theorem smul_resTop_injective (u : Γ(M, ⊤)) {W : X.Opens} (hW : W ≤ nonvanishingOpen X M u)
    {a b : Γ(X, W)} (h : a • resTop W u = b • resTop W u) : a = b :=
  (Stacks.NonvanishingSpelling.bijective_smul X M u hW).1 h

/-- **Division by a nonvanishing global section.** Over an open inside `X_u` every global section
`t` of `M` has a ratio by `u`. -/
theorem exists_resTop_eq_smul (u t : Γ(M, ⊤)) {W : X.Opens} (hW : W ≤ nonvanishingOpen X M u) :
    ∃ f : Γ(X, W), resTop W t = f • resTop W u :=
  let ⟨f, hf⟩ := (Stacks.NonvanishingSpelling.bijective_smul X M u hW).2 (resTop W t)
  ⟨f, hf.symm⟩

end Ratio

/-! ### The finite affine cover, in one degree -/

section Cover

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **Ampleness, in the section ring's vocabulary.** Every point lies in an affine `X_b` for `b` a
homogeneous element of the section ring of positive degree. This is
`Stacks.Ample.IsAmpleForPowers.exists_affine_nonvanishingLocus` carried across
`Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`, which is the vocabulary in which the
powers of a section are available. -/
theorem exists_pos_affine_nvOpen (hL : IsAmple X L) (x : X) :
    ∃ (d : ℕ) (b : powSections L d), 1 ≤ d ∧ x ∈ nvOpen L b ∧ IsAffineOpen (nvOpen L b) := by
  obtain ⟨d, hd, s, W, hW, hxW, hWaff⟩ :=
    IsAmpleForPowers.exists_affine_nonvanishingLocus (pow := tensorPowModule X L) hL x
  obtain ⟨b, hb⟩ := exists_powSections_nvLocus_eq L d s
  have hWeq : nvOpen L b = W := TopologicalSpace.Opens.ext (by rw [coe_nvOpen, hb, hW])
  exact ⟨d, b, hd, hWeq ▸ hxW, hWeq ▸ hWaff⟩

/-- **The cover the gluing argument of Stacks Tag 01PW runs over.** For `L` ample and `a` a
homogeneous element of positive degree `n`, there is one degree `N` carrying both a power `a'` of
`a` — with the same nonvanishing locus, so the open `X_a` is unchanged — and a *finite* family of
homogeneous elements `c i` of that same degree whose nonvanishing loci are affine and cover `X`.

Three facts from the library, in this order: ampleness gives the pointwise affine cover
(`exists_pos_affine_nvOpen`), quasi-compactness cuts it down to a `Finset` of points, and
`Stacks.FinGenFromCover.exists_common_degree_family` followed by one application of
`Stacks.AmpleAffineAvoidance.exists_pow_of_dvd` puts the whole family *and* `a` in the single
degree `N = n * N₀`.

Having one common degree is what makes the rest of the argument statable: on `X_{c i}` the
section `a'` is a scalar multiple of `c i`, which needs the two to be sections of the same
module. -/
theorem exists_common_degree_affine_cover (hL : IsAmple X L) {n : ℕ} (hn : 1 ≤ n)
    (a : powSections L n) :
    ∃ (N : ℕ) (a' : powSections L N) (F : Finset X)
      (c : {y : X // y ∈ F} → powSections L N),
      1 ≤ N ∧ n ∣ N ∧ nvLocus L a' = nvLocus L a ∧ (∀ i, IsAffineOpen (nvOpen L (c i))) ∧
        (⊤ : X.Opens) ≤ ⨆ i, nvOpen L (c i) := by
  have := hL.compactSpace
  choose d b hd hmem haff using exists_pos_affine_nvOpen L hL
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun y : X => nvLocus L (b y))
    (fun y => Stacks.FinGenFromCover.isOpen_nvLocus L (b y))
    fun x _ => Set.mem_iUnion.mpr ⟨x, by simpa [← coe_nvOpen] using hmem x⟩
  obtain ⟨N₀, b', hN₀, hb'⟩ :=
    Stacks.FinGenFromCover.exists_common_degree_family L (ι := {y : X // y ∈ F})
      (fun i => d i.1) (fun i => hd i.1) fun i => b i.1
  have hN : 1 ≤ n * N₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨a', ha'⟩ := Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L a (dvd_mul_right n N₀) hN
  choose c hc using fun i =>
    Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L (b' i) (dvd_mul_left N₀ n) hN
  have hcoe : ∀ i, nvOpen L (c i) = nvOpen L (b i.1) := fun i =>
    TopologicalSpace.Opens.ext (by rw [coe_nvOpen, coe_nvOpen, hc i, hb' i])
  refine ⟨n * N₀, a', F, c, hN, dvd_mul_right n N₀, ha', fun i => (hcoe i) ▸ haff i.1, ?_⟩
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ?_⟩
  rw [hcoe ⟨y, hy⟩]
  simpa [← coe_nvOpen] using hxy

end Cover

/-! ### Restriction plumbing -/

section Plumbing

variable {X : Scheme.{u}}

/-- Restricting twice is restricting once, for the structure sheaf. -/
theorem map_res_res {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op x)
      = X.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting twice is restricting once, for an `𝒪_X`-module. -/
theorem map_res_res_module {M : X.Modules} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op x)
      = M.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Restricting the restriction of a global section**, in this file's spelling of `resTop`.
`Stacks.TensorPowerTrivialize.res_resTop` says the same thing with the sibling file's spelling,
which is a different constant and therefore invisible to `rw` here. -/
theorem res_resTop {M : X.Modules} (u : Γ(M, ⊤)) {W W' : X.Opens} (h : W' ≤ W) :
    M.presheaf.map (homOfLE h).op (resTop W u) = resTop W' u :=
  Stacks.TensorPowerTrivialize.res_resTop M u (homOfLE h)

/-- A finite family of natural numbers is bounded. The finitely many exponents produced by the
local extension and by the annihilator step of Stacks Tag 01PW are raised to a single one this
way. -/
theorem exists_forall_le {ι : Type*} [Finite ι] (e : ι → ℕ) : ∃ k : ℕ, ∀ i, e i ≤ k := by
  have : Fintype ι := Fintype.ofFinite ι
  exact ⟨Finset.univ.sup e, fun i => Finset.le_sup (Finset.mem_univ i)⟩

end Plumbing

/-! ### The gluing argument -/

section Glue

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- `Stacks.AmpleFiniteAvoidance.nvOpen` is `Stacks.NonvanishingOpen.nonvanishingOpen` at the
global section attached to a homogeneous element. -/
theorem nvOpen_eq {k : ℕ} (s : powSections L k) :
    nvOpen L s = nonvanishingOpen X (natTensorPow L k) (globalSection X _ s) := rfl

/-- Let `a` and `c i` be sections of `L ^ N` such that the nonvanishing opens `X_{c i}` are affine
and cover `X`, and let `g` be a function on `U = X_a`. Then there are an exponent `p` and global
sections `t`, `σ` of `L ^ p` with `U ⊆ X_σ` and `t|_U = g • σ|_U`. -/
theorem exists_ratio_of_affine_cover {N : ℕ} (a : powSections L N)
    {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, nvOpen L (c i) = V i)
    (hcaff : ∀ i, IsAffineOpen (V i)) (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
    (g : Γ(X, U)) :
    ∃ (p : ℕ) (t σ : Γ(natTensorPow L p, ⊤)),
      U ≤ nonvanishingOpen X (natTensorPow L p) σ ∧ resTop U t = g • resTop U σ := by
  classical
  have hVle : ∀ i, V i ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) :=
    fun i => le_of_eq (hV i).symm
  -- the ratio `f i = a / c i` over `V i = X_{c i}`
  choose f hf using fun i : ι => exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ a) (hVle i)
  -- `U ⊓ V i` is the basic open of that ratio
  have hD : ∀ i, U ⊓ V i = X.basicOpen (f i) := fun i => by
    rw [← hU]
    exact nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i)) (globalSection X _ a)
      (hVle i) (f i) (hf i)
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i => by rw [← hD i]; exact inf_le_left
  have hDV : ∀ i, X.basicOpen (f i) ≤ V i := fun i => X.basicOpen_le (f i)
  -- the local extension over the affine `V i`, with the exponent raised to a single `k`
  choose e z hz using fun i : ι => AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen X
    (V i) (hcaff i) (f i) (X.presheaf.map (homOfLE (hDU i)).op g)
  obtain ⟨k, hk⟩ := exists_forall_le e
  obtain ⟨cn, hcn⟩ : ∃ cn : (i : ι) → Γ(X, V i), ∀ (i : ι) {S : X.Opens}
      (h : S ≤ X.basicOpen (f i)) (hSV : S ≤ V i) (hSU : S ≤ U),
      X.presheaf.map (homOfLE hSV).op (cn i)
        = X.presheaf.map (homOfLE hSV).op (f i) ^ k * X.presheaf.map (homOfLE hSU).op g := by
    refine ⟨fun i => f i ^ (k - e i) * z i, fun i S h hSV hSU => ?_⟩
    have h0 : X.presheaf.map (homOfLE (hDV i)).op (z i)
        = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ e i
          * X.presheaf.map (homOfLE (hDU i)).op g := hz i
    change X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i ^ (k - e i) * z i)
      = X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i) ^ k
          * X.presheaf.map (homOfLE (h.trans (hDU i))).op g
    rw [← map_res_res h (hDV i) (f i ^ (k - e i) * z i)]
    simp only [map_mul, map_pow, h0, map_res_res]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hk i)]
  -- the ratio `w i j = c j / c i` on the overlap `V i ⊓ V j`
  have hVij : ∀ i j : ι,
      V i ⊓ V j ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) :=
    fun i j => inf_le_left.trans (hVle i)
  choose w hw using fun (i j : ι) => exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ (c j)) (hVij i j)
  obtain ⟨fA, hfA⟩ : ∃ fA : (i j : ι) → Γ(X, V i ⊓ V j), ∀ i j,
      fA i j = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i) :=
    ⟨_, fun _ _ => rfl⟩
  -- `f i = f j * w i j` on the overlap: both compute `a` against `c i`
  have hfw : ∀ i j : ι, fA i j
      = X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j) * w i j := by
    intro i j
    rw [hfA]
    refine smul_resTop_injective (natTensorPow L N) (globalSection X _ (c i)) (hVij i j) ?_
    rw [← resTop_eq_smul_of_le (natTensorPow L N) (inf_le_left : V i ⊓ V j ≤ V i) (f i) (hf i),
      mul_smul, ← hw i j,
      ← resTop_eq_smul_of_le (natTensorPow L N) (inf_le_right : V i ⊓ V j ≤ V j) (f j) (hf j)]
  -- the overlaps are affine, by Stacks Tag 01PV
  have hAaff : ∀ i j : ι, IsAffineOpen (V i ⊓ V j) := fun i j => by
    rw [← hV j]
    exact Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
      (natTensorPow L N) (globalSection X _ (c j)) (hcaff i)
  have hBA : ∀ i j : ι, X.basicOpen (fA i j) ≤ V i ⊓ V j := fun i j => X.basicOpen_le _
  have hBD : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f i) := fun i j => by
    rw [hfA, X.basicOpen_res]; exact inf_le_right
  have hBU : ∀ i j : ι, X.basicOpen (fA i j) ≤ U := fun i j => (hBD i j).trans (hDU i)
  have hBD' : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f j) := fun i j => by
    rw [← hD j]
    exact le_inf (hBU i j) ((hBA i j).trans inf_le_right)
  -- the two numerators agree where `a` does not vanish, so a power of `f i` kills the difference
  have hzero : ∀ i j : ι, X.presheaf.map (homOfLE (hBA i j)).op
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
        = 0 := by
    intro i j
    have hfib : X.presheaf.map (homOfLE ((hBD i j).trans (hDV i))).op (f i)
        = X.presheaf.map (homOfLE ((hBD' i j).trans (hDV j))).op (f j)
            * X.presheaf.map (homOfLE (hBA i j)).op (w i j) := by
      have h := congrArg (X.presheaf.map (homOfLE (hBA i j)).op)
        ((hfA i j).symm.trans (hfw i j))
      rw [map_mul, map_res_res, map_res_res] at h
      exact h
    have key : X.presheaf.map (homOfLE ((hBD i j).trans (hDV i))).op (cn i)
        = X.presheaf.map (homOfLE ((hBD' i j).trans (hDV j))).op (cn j)
            * X.presheaf.map (homOfLE (hBA i j)).op (w i j) ^ k := by
      rw [hcn i (hBD i j) ((hBD i j).trans (hDV i)) (hBU i j),
        hcn j (hBD' i j) ((hBD' i j).trans (hDV j)) (hBU i j), hfib]
      ring
    rw [map_sub, map_mul, map_pow, map_res_res, map_res_res, sub_eq_zero]
    exact key
  choose m hm using fun (i j : ι) =>
    AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X
      (hAaff i j).isCompact
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
      (fA i j) (hzero i j)
  obtain ⟨q, hq⟩ := exists_forall_le fun p : ι × ι => m p.1 p.2
  have hm' : ∀ i j : ι, fA i j ^ (q + 1) *
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
      = fA i j ^ (q + 1) *
        (X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k) := by
    intro i j
    have h := hm i j
    rw [mul_sub, sub_eq_zero] at h
    have hmq : m i j ≤ q := hq (i, j)
    rw [show q + 1 = q + 1 - m i j + m i j by omega, pow_add, mul_assoc, h, mul_assoc]
  -- the exponent of the answer: `K + 1 = k + (q + 1)`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = k + (q + 1) := ⟨k + q, by omega⟩
  -- the two power laws of the compatible family of generators `c i ^ (K + 1)`
  have hσ : ∀ i, resTop (V i) (globalSection X _ (sectionPow L a K))
      = f i ^ (K + 1) • resTop (V i) (globalSection X _ (sectionPow L (c i) K)) := fun i =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) a (f i) (hf i) K
  have hβ : ∀ i j : ι, resTop (V i ⊓ V j) (globalSection X _ (sectionPow L (c j) K))
      = w i j ^ (K + 1) • resTop (V i ⊓ V j)
          (globalSection X _ (sectionPow L (c i) K)) := fun i j =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) (c j) (w i j) (hw i j) K
  -- the numerators agree on the overlaps, by the annihilator and `f i = f j * w i j`
  have hγA : ∀ i j : ι,
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i ^ (q + 1) * cn i)
      = X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j ^ (q + 1) * cn j)
          * w i j ^ (K + 1) := by
    intro i j
    rw [map_mul, map_pow, map_mul, map_pow, ← hfA i j, hm' i j, hfw i j, hK]
    ring
  -- and they compute `g` against the generator over `U ⊓ V i`
  have hγD : ∀ i, X.presheaf.map (homOfLE (hDV i)).op (f i ^ (q + 1) * cn i)
      = X.presheaf.map (homOfLE (hDU i)).op g *
          X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) := by
    intro i
    rw [map_mul, map_pow, hcn i le_rfl (hDV i) (hDU i), hK, pow_add]
    ring
  -- the local sections, and their compatibility
  have hcompat0 : ∀ i j : ι,
      (natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
          ((f i ^ (q + 1) * cn i) • resTop (V i) (globalSection X _ (sectionPow L (c i) K)))
        = (natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
          ((f j ^ (q + 1) * cn j) • resTop (V j)
            (globalSection X _ (sectionPow L (c j) K))) := by
    intro i j
    simp only [Scheme.Modules.map_smul, res_resTop]
    rw [hβ i j, smul_smul, hγA i j]
  have hcompat : TopCat.Presheaf.IsCompatible (natTensorPow L (powDeg N K)).presheaf V
      (fun i => (f i ^ (q + 1) * cn i) •
        resTop (V i) (globalSection X _ (sectionPow L (c i) K))) := hcompat0
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(natTensorPow L (powDeg N K)).presheaf, (natTensorPow L (powDeg N K)).isSheaf⟩ :
      TopCat.Sheaf Ab X) V ⊤ (fun _ => homOfLE le_top) hcover _ hcompat
  refine ⟨powDeg N K, t, globalSection X _ (sectionPow L a K), ?_, ?_⟩
  · rw [← hU]
    exact le_of_eq (Stacks.TensorPowerTrivialize.nonvanishingOpen_sectionPow L a K).symm
  · refine TopCat.Presheaf.IsSheaf.section_ext
      (natTensorPow L (powDeg N K)).isSheaf (U := op U) ?_
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover (TopologicalSpace.Opens.mem_top x))
    refine ⟨X.basicOpen (f i), hDU i, ?_, ?_⟩
    · rw [← hD i]; exact ⟨hx, hi⟩
    · have hti : resTop (V i) t = (f i ^ (q + 1) * cn i) •
          resTop (V i) (globalSection X _ (sectionPow L (c i) K)) := ht i
      rw [res_resTop, ← res_resTop t (hDV i), hti]
      simp only [Scheme.Modules.map_smul, res_resTop]
      rw [resTop_eq_smul_of_le (natTensorPow L (powDeg N K)) (hDV i) (f i ^ (K + 1)) (hσ i),
        map_pow, smul_smul, hγD i]

/-- **The vocabulary bridge for a ratio.** A pair of global sections of
`Stacks.TensorPowers.natTensorPow L p` in the ratio relation gives a pair of global sections of
`Stacks.Ample.tensorPowModule X L p` in the same relation. The two modules are *equal* by
`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow`, so the comparison is an `eqToIso`;
`Stacks.Ample.nonvanishingLocus_congr` transports the locus and
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul` transports the scalar. -/
theorem exists_tensorPow_ratio {p : ℕ} (t σ : Γ(natTensorPow L p, ⊤)) {W : X.Opens}
    (g : Γ(X, W)) (hle : W ≤ nonvanishingOpen X (natTensorPow L p) σ)
    (heq : resTop W t = g • resTop W σ) :
    ∃ t' σ' : Γ(tensorPowModule X L (p : ℤ), ⊤),
      W ≤ Stacks.AmpleTheory.powNonvanishingOpen X L p σ' ∧
        resTop W t' = g • resTop W σ' := by
  have hmod : (natTensorPow L p : X.Modules) = tensorPowModule X L (p : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L p
  refine ⟨(eqToIso (C := X.Modules) hmod).hom.app ⊤ t,
    (eqToIso (C := X.Modules) hmod).hom.app ⊤ σ, ?_, ?_⟩
  · refine hle.trans (le_of_eq (TopologicalSpace.Opens.ext ?_))
    rw [coe_nonvanishingOpen, Stacks.AmpleTheory.coe_powNonvanishingOpen,
      nonvanishingLocus_congr (eqToIso (C := X.Modules) hmod) σ]
  · rw [resTop_app, resTop_app, heq, Scheme.Modules.Hom.app_smul]

/-- **Stacks Tag 01PW, the surjectivity half, for an ample invertible module.**

For `L` ample, every function `g` on a nonvanishing locus `X_s` of a global section of a positive
tensor power of `L` is the ratio `t / σ` of two global sections of one and the same tensor power
of `L`, with `σ` nowhere vanishing on `X_s`. This is
`Stacks.SectionExtension.IsSectionRatio`, the single open declaration of the ample cluster,
**proved under the additional hypothesis that `L` is ample**.

The hypothesis is genuinely additional: Stacks Tag 01PW asks only that `X` be quasi-compact (and,
for the bijectivity half, quasi-separated), with `L` an arbitrary invertible module. See the
module documentation for what is and is not claimed, and why no Stacks attribute is attached. -/
theorem isSectionRatio_of_isAmple (hL : IsAmple X L) : IsSectionRatio X L := by
  intro n hn s g
  obtain ⟨a₀, ha₀⟩ := exists_powSections_nvLocus_eq L n s
  obtain ⟨N, a, F, c, -, -, ha, hcaff, hcover⟩ := exists_common_degree_affine_cover L hL hn a₀
  obtain ⟨p, t, σ, hle, heq⟩ := exists_ratio_of_affine_cover L a c
    (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
    (TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, ha, ha₀, Stacks.AmpleTheory.coe_powNonvanishingOpen]))
    (fun i => nvOpen L (c i)) (fun _ => rfl) hcaff hcover g
  obtain ⟨t', σ', h1, h2⟩ := exists_tensorPow_ratio L t σ g hle heq
  exact ⟨p, t', σ', h1, h2⟩

end Glue

/-! ### The power operation of `Stacks.SectionExtension.Powers`, unconditionally -/

section PowSec

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

omit [IsInvertibleModule X L] in
/-- **The nonvanishing locus of the first power.** `Stacks.SectionExtension.powSec L a 1` is `a`
composed with the degree transport `d = 0 + d`, because multiplication by the unit of the section
ring is exactly that transport (`Stacks.GradedSections.mulMap_id`), and a transport leaves the
nonvanishing locus alone (`Stacks.AmpleAffineAvoidance.nvLocus_comp_eqToHom`).

This is the case `k = 1` that `Stacks.SectionExtension.nvLocus_powSec` carries as the hypothesis
`h1`. That file's "What is not done" proposed discharging it by identifying the nonvanishing
locus of the unit section of the section ring with all of `X`; no such lemma is needed, because
`mulMap_id` removes the unit section from the statement before any locus is computed. -/
theorem nvLocus_powSec_one {d : ℕ} (a : powSections L d) :
    nvLocus L (powSec L a 1) = nvLocus L a := by
  rw [powSec_succ, powSec_zero, Stacks.GradedSections.mul_def,
    Stacks.GradedSections.mulMap_id]
  exact Stacks.AmpleAffineAvoidance.nvLocus_comp_eqToHom L (Nat.zero_add d).symm a

/-- **`X_{a^k} = X_a` for `k ≥ 1`, with no hypothesis.**
`Stacks.SectionExtension.nvLocus_powSec` with its first case discharged by
`nvLocus_powSec_one`. -/
theorem nvLocus_powSec_of_one_le {d : ℕ} (a : powSections L d) (k : ℕ) (hk : 1 ≤ k) :
    nvLocus L (powSec L a k) = nvLocus L a :=
  nvLocus_powSec L a (nvLocus_powSec_one L a) k hk

end PowSec

end Stacks.SectionExtension

end
