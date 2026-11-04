module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.CoverInduction
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.CoverNumber
public import StacksCore.Tactic.StacksAttribute

/-!
# A degree bound for the cohomology of quasi-coherent modules, uniform in the module

Let `X` be a scheme. The cohomology of a quasi-coherent module vanishes in positive degrees on
an affine open ([Stacks, Tag 01XB]), and Mayer--Vietoris propagates such vanishing along a cover
by two opens at the cost of one degree. Running that over a finite cover gives a degree beyond
which the cohomology of *every* quasi-coherent module vanishes, depending on the scheme and the
cover alone.

Two bounds come out of this. For a quasi-compact `X` with affine diagonal the bound is the
affine covering number `t(X)` itself, which is [Stacks, Tag 01XI]. For a quasi-compact
quasi-separated `X` covered by quasi-compact opens `U 1, …, U n` each of which has affine
diagonal — for instance each separated, or affine — the bound is

`d = max { |I| + t(⋂_{i ∈ I} U i) - 1 : ∅ ≠ I ⊆ {1, …, n} }`,

which is [Stacks, Tag 071L]. Note that `X` quasi-separated and the `U i` quasi-compact makes
every `t(⋂_{i ∈ I} U i)` finite, so `d` is a genuine natural number.

## Main definitions

* `AlgebraicGeometry.Scheme.coverDegreeBound`: the number `d` above.

## Main results

* `AlgebraicGeometry.isZero_cohomology_of_affineCoverNum_le`: **[Stacks, Tag 01XI]**.
* `AlgebraicGeometry.isZero_cohomology_of_coverDegreeBound_le` and
  `AlgebraicGeometry.isZero_cohomology_of_coverDegreeBound_le_of_isSeparated`:
  **[Stacks, Tag 071L]**, the second with the covering hypothesis in the source's form.
* `AlgebraicGeometry.isZero_cohomology_of_affineCoverNum_le_of_isCompact`: the open-subscheme
  form of [Stacks, Tag 01XI], which is what the proof of [Stacks, Tag 071L] consumes.
* `AlgebraicGeometry.isAffineOpen_inf_of_le`: inside an open with affine diagonal the
  intersection of two affine opens is affine.
* `AlgebraicGeometry.isZero_Hgroup_bot`: cohomology over the empty open vanishes in every
  degree.

## Implementation notes

The hypothesis "`U` has affine diagonal" is taken in the intrinsic form *the intersection of two
affine opens contained in `U` is affine*, which for `U = ⊤` is one of the equivalent conditions
of [Stacks, Tag 0BDX] and in general is that condition for the open subscheme `U`. This is
weaker than the source's "separated", and phrasing it on opens of the ambient scheme avoids
transporting cohomology along the open immersion `U ⟶ X`. For the same reason the affine covering
number `t(U)` counts affine opens of `X` contained in `U` rather than affine opens of the scheme
`U`; the two agree.

The combinatorial induction is
`Stacks.Cohomology.UniformVanishing.isZero_sheafCohomology_finsetSup`, carried out for
`Ext`-theoretic sheaf cohomology because that is where the Mayer--Vietoris long exact sequence
of [Stacks, Tag 01EB] lives; `AlgebraicGeometry.hgroupIsoSheafCohomology` moves
the result back to the derived functors of `Γ(U, -)` on `Mod(𝒪_X)`, in which the source's
statement and [Stacks, Tag 01XB] are phrased. That comparison exists only in positive degrees,
so degree `0` is treated separately: a bound of `0` forces the open to be empty, where the
cohomology vanishes in every degree by `isZero_Hgroup_bot`.

## References

* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.UniformVanishing

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Cohomology over the empty open -/

/-- **Cohomology over the empty open vanishes in every degree**, including degree `0`. In degree
`0` the cohomology is the group of sections over the empty open, which is a zero group; in
positive degrees this is `Stacks.Cohomology.UniformVanishing.isZero_sheafCohomology_bot` read
through `hgroupIsoSheafCohomology`. -/
theorem isZero_Hgroup_bot (F : X.Modules) (p : ℕ) :
    IsZero (Hgroup X.ringCatSheaf (⊥ : X.Opens) p F) := by
  have hbot : (⊥ : Sieve (⊥ : X.Opens)) ∈ Opens.grothendieckTopology X (⊥ : X.Opens) :=
    (Opens.mem_grothendieckTopology (T := X) (U := ⊥) (S := ⊥)).2 (by simp)
  cases p with
  | zero =>
      have hpl : PreservesFiniteLimits (secF X.ringCatSheaf (⊥ : X.Opens)) :=
        inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf ⋙
          sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (⊥ : X.Opens))))
      have hterm : IsZero ((secF X.ringCatSheaf (⊥ : X.Opens)).obj F) :=
        (Sheaf.isTerminalOfBotCover ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
          (⊥ : X.Opens) hbot).isZero
      exact hterm.of_iso ((secF X.ringCatSheaf (⊥ : X.Opens)).rightDerivedZeroIsoSelf.app F)
  | succ n =>
      have : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
        hasExt_of_enoughInjectives _
      exact (isZero_sheafCohomology_bot F.toAbelianSheaf (n + 1)).of_iso
        (hgroupIsoSheafCohomology F ⊥ n)

/-! ### Finite intersections of affine opens -/

/-- A nonempty finite intersection of affine opens contained in a region where intersections of
two affine opens are affine is itself affine. -/
theorem isAffineOpen_finsetInf {W : X.Opens}
    (hinf : ∀ A B : X.Opens, A ≤ W → B ≤ W → IsAffineOpen A → IsAffineOpen B →
      IsAffineOpen (A ⊓ B))
    {ι : Type*} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hVW : ∀ i, V i ≤ W)
    {s : Finset ι} (hs : s.Nonempty) : IsAffineOpen (s.inf V) := by
  classical
  have hle : ∀ {t : Finset ι}, t.Nonempty → t.inf V ≤ W := by
    intro t ht
    obtain ⟨j, hj⟩ := ht
    exact (Finset.inf_le hj).trans (hVW j)
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hV i
  | cons i s hi hs ih =>
      rw [Finset.inf_cons]
      exact hinf _ _ (hVW i) (hle hs) (hV i) ih

/-- **The intersection of two affine opens inside an open with affine diagonal is affine.**
This is the condition of [Stacks, Tag 0BDX] for the open subscheme `W`, read back on opens of
the ambient scheme: a hypothesis on `W` alone, satisfied in particular when `W` is separated or
affine. -/
theorem isAffineOpen_inf_of_le (W : X.Opens)
    [IsAffineHom (pullback.diagonal (terminal.from W.toScheme))]
    {A B : X.Opens} (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hAW : A ≤ W) (hBW : B ≤ W) :
    IsAffineOpen (A ⊓ B) := by
  have hA' : IsAffineOpen (W.ι ⁻¹ᵁ A) := hA.preimage_of_isOpenImmersion W.ι (by simpa using hAW)
  have hB' : IsAffineOpen (W.ι ⁻¹ᵁ B) := hB.preimage_of_isOpenImmersion W.ι (by simpa using hBW)
  have himg : W.ι ''ᵁ (W.ι ⁻¹ᵁ A ⊓ W.ι ⁻¹ᵁ B) = A ⊓ B := by
    rw [show W.ι ⁻¹ᵁ A ⊓ W.ι ⁻¹ᵁ B = W.ι ⁻¹ᵁ (A ⊓ B) from rfl,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
    simpa using inf_le_left.trans hAW
  rw [← himg]
  exact (hA'.inf hB').image_of_isOpenImmersion W.ι

/-! ### The bound of a single quasi-compact open with affine diagonal -/

section Comparison

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Positive-degree vanishing transfers from `Ext`-theoretic sheaf cohomology to the derived
functors of `Γ(U, -)`; in degree `0` the open must be empty, and then the cohomology vanishes
anyway. -/
private theorem isZero_Hgroup_of_isZero_sheafCohomology (F : X.Modules) (W : X.Opens) (p : ℕ)
    (hbot : p = 0 → W = ⊥) (h : IsZero (Sheaf.H' F.toAbelianSheaf p W)) :
    IsZero (Hgroup X.ringCatSheaf W p F) := by
  cases p with
  | zero =>
      rw [hbot rfl]
      exact isZero_Hgroup_bot F 0
  | succ n => exact h.of_iso (hgroupIsoSheafCohomology F W n)

/-- Mayer--Vietoris induction over a finite family of opens with union `W`, in the form of
`isZero_sheafCohomology_finsetSup` for the whole index type. -/
private theorem isZero_sheafCohomology_of_iSup_eq (F : X.Modules) {ι : Type*} [Finite ι]
    (V : ι → X.Opens) (W : X.Opens) (hW : ⨆ i, V i = W) (τ : Finset ι → ℕ) (d : ℕ)
    (h₁ : ∀ s : Finset ι, s.Nonempty → ∀ p : ℕ, τ s ≤ p →
      IsZero (Sheaf.H' F.toAbelianSheaf p (s.inf V)))
    (h₂ : ∀ s : Finset ι, s.Nonempty → s.card + τ s - 1 ≤ d) (p : ℕ) (hp : d ≤ p) :
    IsZero (Sheaf.H' F.toAbelianSheaf p W) := by
  have := Fintype.ofFinite ι
  rw [← hW, ← Finset.sup_univ_eq_iSup]
  exact isZero_sheafCohomology_finsetSup F.toAbelianSheaf Finset.univ V τ d h₁
    (fun s _ => h₂ s) p hp

/-- [Stacks, Tag 01XI] for the `Ext`-theoretic sheaf cohomology of the underlying abelian sheaf:
over a quasi-compact open in which intersections of affine opens are affine, the cohomology of a
quasi-coherent module vanishes in degrees at least the affine covering number. -/
private theorem isZero_sheafCohomology_of_affineCoverNum_le (F : X.Modules) [F.IsQuasicoherent]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (hinf : ∀ A B : X.Opens, A ≤ W → B ≤ W → IsAffineOpen A → IsAffineOpen B →
      IsAffineOpen (A ⊓ B))
    (p : ℕ) (hp : X.affineCoverNum W ≤ p) :
    IsZero (Sheaf.H' F.toAbelianSheaf p W) := by
  classical
  obtain ⟨V, hVaff, hVcov⟩ := Scheme.exists_affineCover_affineCoverNum W hW
  have hVW : ∀ i, V i ≤ W := fun i => hVcov ▸ le_iSup V i
  refine isZero_sheafCohomology_of_iSup_eq F V W hVcov (fun _ => 1) (X.affineCoverNum W) ?_ ?_ p hp
  · intro s hs pp hpp
    obtain ⟨m, rfl⟩ : ∃ m, pp = m + 1 := ⟨pp - 1, by omega⟩
    exact (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F (s.inf V)
        (isAffineOpen_finsetInf hinf V hVaff hVW hs) (m + 1) (by omega)).of_iso
      (hgroupIsoSheafCohomology F (s.inf V) m).symm
  · intro t _
    simpa using Finset.card_le_univ t

end Comparison

/-- **[Stacks, Tag 01XI] for an open subscheme.** Let `W` be a quasi-compact open of a scheme
such that the intersection of two affine opens contained in `W` is affine — for instance `W`
separated, or affine. Then the cohomology of a quasi-coherent module over `W` vanishes in every
degree at least the affine covering number `t(W)`. -/
theorem isZero_cohomology_of_affineCoverNum_le_of_isCompact (F : X.Modules) [F.IsQuasicoherent]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (hinf : ∀ A B : X.Opens, A ≤ W → B ≤ W → IsAffineOpen A → IsAffineOpen B →
      IsAffineOpen (A ⊓ B))
    (p : ℕ) (hp : X.affineCoverNum W ≤ p) :
    IsZero (Hgroup X.ringCatSheaf W p F) := by
  have : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  refine isZero_Hgroup_of_isZero_sheafCohomology F W p (fun hp0 => ?_)
    (isZero_sheafCohomology_of_affineCoverNum_le F W hW hinf p hp)
  exact Scheme.eq_bot_of_affineCoverNum_eq_zero W hW (by omega)

/-- **Stacks Project, Tag 01XI.** Let `X` be a quasi-compact scheme with affine diagonal — for
instance a separated scheme — and let `t = t(X)` be the minimal number of affine opens needed to
cover `X`. Then `H^p(X, F) = 0` for every `p ≥ t` and every quasi-coherent `𝒪_X`-module `F`. -/
@[stacks 01XI]
theorem isZero_cohomology_of_affineCoverNum_le (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (F : X.Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : X.affineCoverNum ⊤ ≤ p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) :=
  isZero_cohomology_of_affineCoverNum_le_of_isCompact F ⊤
    (by simpa using isCompact_univ (X := (X : Type u)))
    (fun _ _ _ _ hA hB => hA.inf hB) p hp

/-! ### The bound of a cover by quasi-compact opens with affine diagonal -/

/-- **The degree bound of [Stacks, Tag 071L]** for a finite family of opens `U` of a scheme:
the maximum of `|I| + t(⋂_{i ∈ I} U i) - 1` over the nonempty index sets `I`, where `t` is the
affine covering number `AlgebraicGeometry.Scheme.affineCoverNum`. -/
noncomputable def Scheme.coverDegreeBound (X : Scheme.{u}) {n : ℕ} (U : Fin n → X.Opens) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).erase ∅).sup
    fun s => s.card + X.affineCoverNum (s.inf U) - 1

/-- The defining property of `AlgebraicGeometry.Scheme.coverDegreeBound`: it dominates
`|I| + t(⋂_{i ∈ I} U i) - 1` for every nonempty `I`. -/
theorem Scheme.le_coverDegreeBound (X : Scheme.{u}) {n : ℕ} (U : Fin n → X.Opens)
    {s : Finset (Fin n)} (hs : s.Nonempty) :
    s.card + X.affineCoverNum (s.inf U) - 1 ≤ X.coverDegreeBound U :=
  Finset.le_sup (f := fun s => s.card + X.affineCoverNum (s.inf U) - 1)
    (Finset.mem_erase.2 ⟨hs.ne_empty, Finset.mem_univ s⟩)

/-- **[Stacks, Tag 071L] with an arbitrary dominating bound.** Under the hypotheses of
[Stacks, Tag 071L], the cohomology of every quasi-coherent module over `X` vanishes in each
degree at least `d`, for any `d` dominating all the numbers `|I| + t(⋂_{i ∈ I} U i) - 1`. -/
theorem isZero_cohomology_of_cover_bound [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens) (hcov : ⨆ i, U i = ⊤)
    (hUc : ∀ i, IsCompact (U i : Set X))
    (hUinf : ∀ (i : Fin n) (A B : X.Opens), A ≤ U i → B ≤ U i → IsAffineOpen A →
      IsAffineOpen B → IsAffineOpen (A ⊓ B))
    (d : ℕ) (hd : ∀ s : Finset (Fin n), s.Nonempty →
      s.card + X.affineCoverNum (s.inf U) - 1 ≤ d)
    (p : ℕ) (hp : d ≤ p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  classical
  have : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  have hinf : ∀ s : Finset (Fin n), s.Nonempty → ∀ A B : X.Opens, A ≤ s.inf U → B ≤ s.inf U →
      IsAffineOpen A → IsAffineOpen B → IsAffineOpen (A ⊓ B) := by
    intro s hs A B hA hB hAaff hBaff
    obtain ⟨i, hi⟩ := hs
    exact hUinf i A B (hA.trans (Finset.inf_le hi)) (hB.trans (Finset.inf_le hi)) hAaff hBaff
  have hH : IsZero (Sheaf.H' F.toAbelianSheaf p (⊤ : X.Opens)) :=
    isZero_sheafCohomology_of_iSup_eq F U ⊤ hcov (fun s => X.affineCoverNum (s.inf U)) d
      (fun s hs pp hpp => isZero_sheafCohomology_of_affineCoverNum_le F (s.inf U)
        (isCompact_finsetInf U hUc hs) (hinf s hs) pp hpp) hd p hp
  refine isZero_Hgroup_of_isZero_sheafCohomology F ⊤ p (fun hp0 => ?_) hH
  have hd0 : d = 0 := by omega
  have hUbot : ∀ i, U i = ⊥ := by
    intro i
    refine Scheme.eq_bot_of_affineCoverNum_eq_zero (U i) (hUc i) ?_
    have h := hd {i} ⟨i, by simp⟩
    simp only [Finset.card_singleton, Finset.inf_singleton] at h
    omega
  rw [← hcov]
  simp [hUbot]

/-- **Stacks Project, Tag 071L.** Let `X` be a quasi-compact quasi-separated scheme and let
`X = U 1 ∪ … ∪ U n` be an open covering with each `U i` quasi-compact and with affine
diagonal — for instance separated, or affine. Set

`d = max { |I| + t(⋂_{i ∈ I} U i) - 1 : ∅ ≠ I ⊆ {1, …, n} }`,

the `AlgebraicGeometry.Scheme.coverDegreeBound` of the covering, where `t(U)` is the minimal
number of affine opens needed to cover `U`. Then `H^p(X, F) = 0` for all `p ≥ d` and every
quasi-coherent `𝒪_X`-module `F`. -/
@[stacks 071L]
theorem isZero_cohomology_of_coverDegreeBound_le [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens) (hcov : ⨆ i, U i = ⊤)
    (hUc : ∀ i, IsCompact (U i : Set X))
    (hUinf : ∀ (i : Fin n) (A B : X.Opens), A ≤ U i → B ≤ U i → IsAffineOpen A →
      IsAffineOpen B → IsAffineOpen (A ⊓ B))
    (p : ℕ) (hp : X.coverDegreeBound U ≤ p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) :=
  isZero_cohomology_of_cover_bound F U hcov hUc hUinf (X.coverDegreeBound U)
    (fun _ hs => X.le_coverDegreeBound U hs) p hp

/-- **Stacks Project, Tag 071L**, with the covering hypothesis in the source's form: each `U i`
is quasi-compact and separated. -/
@[stacks 071L]
theorem isZero_cohomology_of_coverDegreeBound_le_of_isSeparated [CompactSpace X]
    [QuasiSeparatedSpace X] (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens)
    (hcov : ⨆ i, U i = ⊤) (hUc : ∀ i, IsCompact (U i : Set X))
    (hUsep : ∀ i, (U i).toScheme.IsSeparated)
    (p : ℕ) (hp : X.coverDegreeBound U ≤ p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  refine isZero_cohomology_of_coverDegreeBound_le F U hcov hUc
    (fun i A B hAW hBW hA hB => ?_) p hp
  have _ := hUsep i
  exact isAffineOpen_inf_of_le (U i) hA hB hAW hBW

end AlgebraicGeometry
