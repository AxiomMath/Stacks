module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.Coordinates
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.TwistedCech
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.PartOne.Basic
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout

/-!
# Ampleness ascends along a first-order thickening

Let `k : Y ⟶ Y'` be a first-order thickening — a closed immersion surjective on points whose
ideal sheaf squares to zero — and let `𝓛'` be an invertible `𝒪_{Y'}`-module. If `k^* 𝓛'` is ample
then so is `𝓛'`.

This is the square-zero case of the hard implication of [Stacks, Tag 09MS], proved with no
Noetherian hypothesis and no cohomology group: the cohomological lift of the source is replaced by
the Čech computation `Stacks.AmpleThickeningAscent.exists_twisted_lift`, carried out in local
coordinates.

## The argument

`Y'` is quasi-compact, being homeomorphic to `Y`, and separated by [Stacks, Tag 09MQ], `Y` being
separated by [Stacks, Tag 09MP]. Fix a finite cover of `Y'` by affine opens `W i` on which `𝓛'` is
trivial, with basis sections `b i`. Given a point `y`, choose `c` with `y ∈ W c`. Since `k^* 𝓛'`
is ample, clause (4) of [Stacks, Tag 01Q3] gives a global section `s` of `(k^* 𝓛') ^ n`, `n ≥ 1`,
whose nonvanishing locus `Y_s` is affine, contains a preimage of `y`, and lies inside `k⁻¹ W c`.
The open `V` of `Y'` with `k⁻¹ V = Y_s` is affine by [Stacks, Tag 06AD] and lies inside `W c`, so
the restriction of `b c` trivializes `𝓛'` over it. Adjoin `V` to the cover.

Against the pulled-back bases `k^* b i ^ n` the section `s` has coordinates `ρ i` transforming by
the `n`-th powers of the pulled-back transition functions, with `D(ρ i) = k⁻¹ (W i ⊓ V)`. The
twisted Čech lift produces functions `f i` on the `W i` transforming by the
`n (N + 1)`-st powers of the transition functions, with `k^♯ f i = ρ i ^ (N + 1)`. They are the
coordinates of a global section `σ` of `𝓛' ^ (n (N + 1))`, and `σ` vanishes exactly off `V`,
because `k⁻¹ D(f i) = D(ρ i) = k⁻¹ (W i ⊓ V)` and `k` is a homeomorphism. So `y` lies in the affine
nonvanishing locus `V` of a global section of a positive power of `𝓛'`.

## Main results

* `Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isFirstOrderThickening`.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.AmpleTheory
open Stacks.Thickenings
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn nonvanishingLocusOn_top)
open Stacks.TensorSectionPower (powObj secPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.AmpleThickeningAscent

variable {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}

/-- **Ampleness ascends along a first-order thickening.** For a first-order thickening
`k : Y ⟶ Y'` and an invertible `𝒪_{Y'}`-module `𝓛'`, ampleness of `k^* 𝓛'` gives ampleness of
`𝓛'`. See the module docstring. -/
theorem isAmple_of_isAmple_pullback_of_isFirstOrderThickening (hk : IsFirstOrderThickening k)
    (L' : Y'.Modules) [IsInvertibleModule Y' L'] (h : IsAmple Y (pullbackModule k L')) :
    IsAmple Y' L' := by
  classical
  have : IsClosedImmersion k := hk.1
  have hT : IsThickening k := hk.isThickening
  have : Surjective k := ⟨hT.2⟩
  have : CompactSpace Y := h.1
  have : CompactSpace Y' := hT.homeomorph.compactSpace
  have : Y.IsSeparated :=
    ((Stacks.AmpleBridge.isAmple_iff_isAmple Y _).mp h).isSeparated
  have : Y'.IsSeparated := Scheme.isSeparated_of_surjective_universallyClosed k
  have hmono : ∀ {V₁ V₂ : Y'.Opens}, k ⁻¹ᵁ V₁ ≤ k ⁻¹ᵁ V₂ → V₁ ≤ V₂ := by
    intro V₁ V₂ h z hz
    obtain ⟨x, rfl⟩ := hT.2 z
    exact h hz
  have hinj : ∀ {V₁ V₂ : Y'.Opens}, k ⁻¹ᵁ V₁ = k ⁻¹ᵁ V₂ → V₁ = V₂ := fun h =>
    le_antisymm (hmono h.le) (hmono h.ge)
  rw [isAmple_iff_forall_affine_nonvanishingOpen]
  refine ⟨inferInstance, fun y => ?_⟩
  -- a trivializing affine cover of `𝓛'`
  obtain ⟨ι, hι, W, hWaff, hWcov, htriv⟩ :=
    Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover L'
  have : Finite ι := hι
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨c, hyc⟩ : ∃ c, y ∈ W c := Opens.mem_iSup.mp (hWcov (Opens.mem_top y))
  obtain ⟨x, rfl⟩ := hT.2 y
  -- an affine nonvanishing locus around `x` inside `k⁻¹ W c`
  obtain ⟨n, hn, s, hsaff, hxs, hsle⟩ :=
    Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple Y (pullbackModule k L') h x
      (k ⁻¹ᵁ W c) hyc
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  set Ys := powNonvanishingOpen Y (pullbackModule k L') (p + 1) s
  obtain ⟨V, hV⟩ : ∃ V : Y'.Opens, k ⁻¹ᵁ V = Ys := ⟨_, hT.preimage_opensCongr Ys⟩
  have hVc : V ≤ W c := hmono (by rw [hV]; exact hsle)
  have hVaff : IsAffineOpen V := (isAffineOpen_iff_isAffineOpen_preimage hT V).mpr (hV ▸ hsaff)
  -- the enlarged cover
  let U : Option ι → Y'.Opens := fun o => o.elim V W
  let τ : ∀ o, Stacks.SheafDescent.Trivialization Y'.presheaf L'.val (U o) := fun o =>
    match o with
    | none => (htriv c).some.comp (homOfLE hVc)
    | some i => (htriv i).some
  have hUaff : ∀ o, IsAffineOpen (U o) := fun o => match o with
    | none => hVaff
    | some i => hWaff i
  have hPaff : ∀ o o', IsAffineOpen (U o ⊓ U o') := fun o o' => (hUaff o).inf (hUaff o')
  have hUcov : (⊤ : Y'.Opens) ≤ ⨆ o, U o := fun z hz => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hWcov hz)
    exact Opens.mem_iSup.mpr ⟨some i, hi⟩
  -- the section in the `powObj` grading
  let σ₀ : Γ(powObj (pullbackModule k L') p, ⊤) :=
    (Stacks.SectionPowerOverOpen.powObjIsoTensorPow (pullbackModule k L') p).inv.app ⊤ s
  have hσ₀ : Stacks.Ample.nonvanishingLocus (powObj (pullbackModule k L') p) σ₀ =
      (k ⁻¹ᵁ V : Set Y) := by
    rw [hV, coe_powNonvanishingOpen, ← nonvanishingLocus_congr
      (Stacks.SectionPowerOverOpen.powObjIsoTensorPow (pullbackModule k L') p).symm s]
    rfl
  -- its coordinates
  obtain ⟨ρ, hρ, hρD⟩ := exists_coordinates_pullback L' τ k p σ₀
  have hD : ∀ o, Y.basicOpen (ρ o) = k ⁻¹ᵁ (U o ⊓ U none) := by
    intro o
    refine SetLike.coe_injective ?_
    rw [hρD, hσ₀]
    rfl
  -- the twisted Čech lift
  obtain ⟨N, f, hf, hkf⟩ := exists_twisted_lift hk U hUaff hPaff (transition L' τ)
    (fun i j l => transition_cocycle L' τ i j l) (p + 1) none ρ hρ hD
  set q := p * (N + 1) + N
  have hq : (p + 1) * (N + 1) = q + 1 := by simp only [q]; ring
  obtain ⟨T, -, hTloc⟩ := exists_section_of_coordinates L' τ hUcov q f fun i j => by
    rw [← hq]; exact hf i j
  -- the nonvanishing locus of the glued section is `V`
  have hbasic : ∀ o, Y'.basicOpen (f o) = U o ⊓ U none := by
    intro o
    refine hinj ?_
    rw [Scheme.preimage_basicOpen, hkf, Y.basicOpen_pow _ (Nat.succ_pos N), hD]
  have hTV : Stacks.Ample.nonvanishingLocus (powObj L' q) T = (V : Set Y') := by
    ext z
    obtain ⟨o, ho⟩ := Opens.mem_iSup.mp (hUcov (Opens.mem_top z))
    have h1 := hTloc o
    rw [hbasic o] at h1
    constructor
    · intro hz
      have : z ∈ ((U o ⊓ U none : Y'.Opens) : Set Y') := h1 ▸ ⟨hz, ho⟩
      exact this.2
    · intro hz
      have : z ∈ ((U o ⊓ U none : Y'.Opens) : Set Y') := ⟨ho, hz⟩
      exact (h1 ▸ this).1
  -- the section of the tensor power
  let s' : Γ(tensorPowModule Y' L' ((q + 1 : ℕ) : ℤ), ⊤) :=
    (Stacks.SectionPowerOverOpen.powObjIsoTensorPow L' q).hom.app ⊤ T
  have hs' : powNonvanishingOpen Y' L' (q + 1) s' = V := by
    refine SetLike.coe_injective ?_
    rw [coe_powNonvanishingOpen, nonvanishingLocus_congr, hTV]
  refine ⟨q + 1, by omega, s', ?_, ?_⟩
  · rw [hs']; exact hVaff
  · rw [hs']
    show x ∈ k ⁻¹ᵁ V
    rw [hV]
    exact hxs

end Stacks.AmpleThickeningAscent

end
