module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.RatioCompactCover
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample
public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.AmpleFiniteSet
public import StacksFrontier.AlgebraicGeometry.AmpleLocallyClosed.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Powers

/-!
# Ampleness from a cover by quasi-affine nonvanishing opens

Let `X` be a quasi-compact quasi-separated scheme and `L` an invertible `𝒪_X`-module. Ampleness
of `L` asks that every point lie in an **affine** nonvanishing open `X_s` of a global section `s`
of a positive tensor power of `L` ([Stacks, Tag 01PS]). This file proves that it is enough for
every point to lie in a **quasi-affine** such `X_s`.

`Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen` is the converse direction — for `L` ample the
nonvanishing open of a homogeneous section of positive degree is quasi-affine — so the condition
proved sufficient here is also necessary.

## Why this is what fpqc descent delivers

Quasi-affineness of a morphism is fpqc local on the base ([Stacks, Tag 02L7]) and affineness of
an *open subscheme* is not something the fibres of an fpqc covering see directly; what descends
from relative ampleness upstairs is exactly the quasi-affineness of each `X_s`. This file is the
step that turns that into ampleness, and it is the last step of `(2) ⟹ (1)` of
[Stacks, Tag 0D2P] in
`StacksFrontier/AlgebraicGeometry/Descent/RelativeAmpleFpqcLocalOnBase.lean`.

## Main results

* `Stacks.AmpleQuasiAffineCover.exists_affine_basicOpen_mem_of_isQuasiAffine`: a point of a
  quasi-affine open `U` of `X` lies in an affine basic open `X_f` of a function `f` on `U`.
The vocabulary bridge from a homogeneous element of the section ring to an honest global section
of a tensor power, with the same nonvanishing locus, is **not** restated here: it is already
`Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq`, which this module imports.
* `Stacks.AmpleQuasiAffineCover.isAmple_of_forall_exists_isQuasiAffine_nvOpen`: **the content**,
  in the section ring's vocabulary.
* `Stacks.AmpleQuasiAffineCover.isAmple_of_forall_exists_isQuasiAffine_nonvanishingOpen`: the
  same with the sections taken to be honest global sections of the tensor powers.

## The route

Fix a point `x`. Quasi-compactness cuts the hypothesis down to a finite family of homogeneous
elements, and `Stacks.FinGenFromCover.exists_common_degree_family` puts them in one degree `N`,
so that `X` is covered by finitely many quasi-affine `V i = X_{c i}` with the `c i` of a single
degree. Let `i` be an index with `x ∈ V i`.

`V i` being quasi-affine, `x` lies in an affine basic open `(V i)_u` of a function `u` on `V i`
(`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`). The surjectivity half of
[Stacks, Tag 01PW] writes `u` as a ratio `t / (c i)^m` with `t` a homogeneous element of degree
`N m` — this is `Stacks.SectionRingChartBijective.exists_ratio_powSec_of_compact_cover`, which is
where the quasi-affineness of the `V i` is spent: it supplies the quasi-compactness and
quasi-separatedness that the gluing argument of Tag 01PW needs of the members of the cover, in
place of the affineness the ample case has. Then
`Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen` reads the ratio backwards as
`X_t ⊓ V i = (V i)_u`, and `X_{(c i) · t} = X_{c i} ⊓ X_t` is that same affine open, carried by a
single homogeneous element of degree `N + N m ≥ 1`.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec resTop nonvanishingOpen_inf_eq_basicOpen
  nvLocus_powSec_of_one_le)

universe u

namespace Stacks.AmpleQuasiAffineCover

/-! ### An affine basic open around a point of a quasi-affine open -/

/-- **A point of a quasi-affine open lies in an affine basic open of a function on that open.**
The affine basic opens of global functions on a quasi-affine scheme form a basis of its topology
(`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`); this transports one of them across
the open immersion `U.ι`, so that it is read as a basic open of `X`.

This is the converse of the step by which
`Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen` deduces quasi-affineness of `X_a` from such a
family of basic opens. -/
theorem exists_affine_basicOpen_mem_of_isQuasiAffine {X : Scheme.{u}} {U : X.Opens}
    (hU : U.toScheme.IsQuasiAffine) {x : X} (hx : x ∈ U) :
    ∃ f : Γ(X, U), IsAffineOpen (X.basicOpen f) ∧ x ∈ X.basicOpen f := by
  have := hU
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen
      U.toScheme).exists_subset_of_mem_open (Set.mem_univ (⟨x, hx⟩ : U.toScheme)) isOpen_univ
  have hinv : U.topIso.inv (U.topIso.hom r) = r := by
    change (U.topIso.hom ≫ U.topIso.inv) r = r
    rw [Iso.hom_inv_id]
    rfl
  refine ⟨U.topIso.hom r, ?_⟩
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv, hinv,
    Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι]
  exact ⟨hr, ⟨x, hx⟩, hxr, rfl⟩

section Monoidal

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

/-! ### The vocabulary bridge, read from the section ring to honest global sections

This file used to restate the bridge itself.  It does not: the statement is already in the
library, twice, and this module imports one of the two.  Consumers below use
`Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq`
(`StacksFrontier/AlgebraicGeometry/FinGenFromCover/Powers.lean`), which is reachable here with no
added import. -/

/-- A global section of a tensor power has the same nonvanishing open as some section-ring
element. -/
private theorem exists_nvOpen_eq_nonvanishingOpen (n : ℕ)
    (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) :
    ∃ a : powSections L n, nvOpen L a = nonvanishingOpen X (tensorPowModule X L (n : ℤ)) s := by
  obtain ⟨a, ha⟩ := exists_powSections_nvLocus_eq L n s
  exact ⟨a, TopologicalSpace.Opens.ext (by rw [coe_nvOpen, ha, coe_nonvanishingOpen])⟩

/-- **The nonvanishing open of a global section of a positive tensor power of an ample module is
quasi-affine.** This is `Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen` with the homogeneous
element of the section ring traded for an honest global section by
`Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`. -/
theorem isQuasiAffine_nonvanishingOpen_of_isAmple (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d)
    (s : Γ(tensorPowModule X L (d : ℤ), ⊤)) :
    (nonvanishingOpen X (tensorPowModule X L (d : ℤ)) s).toScheme.IsQuasiAffine := by
  obtain ⟨a, ha⟩ := exists_nvOpen_eq_nonvanishingOpen L d s
  exact ha ▸ Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen L hL hd a

/-! ### Ampleness from a quasi-affine nonvanishing cover -/

/-- **A cover by quasi-affine nonvanishing opens makes an invertible module ample.** Let `X` be a
quasi-compact quasi-separated scheme and `L` an invertible `𝒪_X`-module. If every point of `X`
lies in the nonvanishing open `X_b` of some homogeneous element `b` of positive degree of the
section ring, and every such `X_b` used is quasi-affine, then `L` is ample.

Ampleness demands *affine* nonvanishing opens; the affine one is produced from the quasi-affine
one by the surjectivity half of [Stacks, Tag 01PW], in the form
`Stacks.SectionRingChartBijective.exists_ratio_powSec_of_compact_cover`. See the module
docstring. -/
theorem isAmple_of_forall_exists_isQuasiAffine_nvOpen [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ x : X, ∃ (d : ℕ) (b : powSections L d), 1 ≤ d ∧ x ∈ nvOpen L b ∧
      (nvOpen L b).toScheme.IsQuasiAffine) :
    IsAmple X L := by
  classical
  choose d b hd hmem hqa using h
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun y : X => nvLocus L (b y))
    (fun y => Stacks.FinGenFromCover.isOpen_nvLocus L (b y))
    fun x _ => Set.mem_iUnion.mpr ⟨x, by simpa [← coe_nvOpen] using hmem x⟩
  obtain ⟨N, c, hN, hc⟩ :=
    Stacks.FinGenFromCover.exists_common_degree_family L (ι := {y : X // y ∈ F})
      (fun i => d i.1) (fun i => hd i.1) fun i => b i.1
  set V : {y : X // y ∈ F} → X.Opens := fun i => nvOpen L (c i) with hVdef
  have hVeq : ∀ i, V i = nvOpen L (b i.1) := fun i =>
    TopologicalSpace.Opens.ext (by rw [hVdef]; simp only [coe_nvOpen]; exact hc i)
  have hVqa : ∀ i, (V i).toScheme.IsQuasiAffine := fun i => (hVeq i) ▸ hqa i.1
  have hVcpt : ∀ i, IsCompact ((V i : X.Opens) : Set X) := fun i => by
    have hq := hVqa i
    rw [isCompact_iff_compactSpace]
    exact hq.toCompactSpace
  have hVqs : ∀ i, IsQuasiSeparated ((V i : X.Opens) : Set X) := fun _ =>
    isQuasiSeparated_univ.of_subset (Set.subset_univ _)
  have hVcap : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X) := fun i j => by
    rw [TopologicalSpace.Opens.coe_inf]
    exact isQuasiSeparated_univ _ _ (Set.subset_univ _) (V i).isOpen (hVcpt i)
      (Set.subset_univ _) (V j).isOpen (hVcpt j)
  have hcover : (⊤ : X.Opens) ≤ ⨆ i, V i := by
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ?_⟩
    rw [hVeq ⟨y, hy⟩]
    simpa [← coe_nvOpen] using hxy
  refine ⟨‹CompactSpace X›, fun x => ?_⟩
  obtain ⟨i, hxi⟩ :=
    TopologicalSpace.Opens.mem_iSup.mp (hcover (TopologicalSpace.Opens.mem_top x))
  obtain ⟨u, huaff, hxu⟩ := exists_affine_basicOpen_mem_of_isQuasiAffine (hVqa i) hxi
  obtain ⟨m, hm, t, ht⟩ := Stacks.SectionRingChartBijective.exists_ratio_powSec_of_compact_cover
    L (c i) c (V i) rfl V (fun _ => rfl) hVcpt hVqs hVcap hcover u
  have hpow : nvOpen L (powSec L (c i) m) = V i :=
    TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, nvLocus_powSec_of_one_le L (c i) m hm, hVdef, coe_nvOpen])
  have hinf : nvOpen L t ⊓ V i = X.basicOpen u :=
    nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (powSec L (c i) m))
      (globalSection X _ t) (le_of_eq hpow.symm) u ht
  obtain ⟨s, hs⟩ :=
    Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq L (N + N * m) (mul (c i) t)
  refine ⟨N + N * m, by omega, s, X.basicOpen u, ?_, hxu, huaff⟩
  rw [hs, nvLocus_mul, ← coe_nvOpen, ← coe_nvOpen, ← TopologicalSpace.Opens.coe_inf,
    show nvOpen L (c i) ⊓ nvOpen L t = nvOpen L t ⊓ V i from inf_comm _ _, hinf]

/-- **A cover by quasi-affine nonvanishing opens makes an invertible module ample**, with the
sections taken to be honest global sections of the integer tensor powers of `L` rather than
homogeneous elements of the section ring. This is
`Stacks.AmpleQuasiAffineCover.isAmple_of_forall_exists_isQuasiAffine_nvOpen` across
`Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`. -/
theorem isAmple_of_forall_exists_isQuasiAffine_nonvanishingOpen
    [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      x ∈ nonvanishingOpen X (tensorPowModule X L (n : ℤ)) s ∧
        (nonvanishingOpen X (tensorPowModule X L (n : ℤ)) s).toScheme.IsQuasiAffine) :
    IsAmple X L := by
  refine isAmple_of_forall_exists_isQuasiAffine_nvOpen L fun x => ?_
  obtain ⟨n, hn, s, hxs, hqa⟩ := h x
  obtain ⟨a, ha⟩ := exists_nvOpen_eq_nonvanishingOpen L n s
  exact ⟨n, a, hn, ha ▸ hxs, ha ▸ hqa⟩

end Monoidal

end Stacks.AmpleQuasiAffineCover

end
