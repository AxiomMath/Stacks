module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksCore.Topology.Compact.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Sections
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Ampleness from vanishing of the first cohomology of ideal sheaves

Let `X` be a quasi-compact scheme and `𝓛` an invertible `𝒪_X`-module. If for every closed
subscheme `i : Z ⟶ X` there is an `n ≥ 1` with `H¹(X, ℐ_i ⊗ 𝓛^{⊗ n}) = 0`, where `ℐ_i` is the
ideal sheaf of `i`, then `𝓛` is ample. This is the content of [Stacks, Tag 0B5P], and it is the
implication (3) `⇒` (1) of [Stacks, Tag 0B5U] that [Stacks, Tag 0B5X] uses for "positive degree
implies ample" on a proper curve.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_sections_mem_isAffineOpen_nonvanishingOpen`: **the
  section the criterion produces.** If `i : Z ⟶ X` is a closed immersion whose image is
  `(X ∖ U) ∪ {y}` for an affine open `U` containing the closed point `y`, and
  `H¹(X, ℐ_i ⊗ 𝒫) = 0` for an invertible `𝒫`, then `𝒫` has a global section `s` with `y ∈ X_s`
  and `X_s` affine.
* `AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_isClosed_singleton`: **ampleness is
  detected at closed points.** On a quasi-compact scheme it is enough to exhibit an affine
  nonvanishing locus of a section of a positive tensor power around every *closed* point.
* `AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_isZero_h1_idealSheaf`: **the
  criterion**, [Stacks, Tag 0B5P] with its hypothesis read over closed subschemes.

## The argument

The source takes a closed point `y`, an affine open `U ∋ y` on which `𝓛` is trivial, and the two
reduced closed subschemes cut out by `Z = X ∖ U` and `Z' = Z ∪ {y}`; it tensors
`0 ⟶ ℐ' ⟶ ℐ ⟶ ℐ/ℐ' ⟶ 0` by `𝓛^{⊗ n}`, computes `Γ(X, ℐ/ℐ' ⊗ 𝓛^{⊗ n}) = A/𝔪` using the
triviality of `𝓛` on `U`, and lifts the unit.

Only one closed subscheme is needed here, and the triviality of `𝓛|_U` is not needed at all.
Take `C = (X ∖ U) ∪ {y}` with its reduced structure `i : Z ⟶ X`. Since `y ∈ U` and
`C ∩ U = {y}`, the singleton `{y}` is *clopen* in `C`, so
`Stacks.Cohomology.AmpleH1.exists_sections_nonvanishingLocus_eq_singleton` gives a global
section `t` of `i^*𝒫` whose nonvanishing locus is exactly that point — this replaces the
computation of `Γ(X, ℐ/ℐ' ⊗ 𝓛^{⊗ n})`. The assumed vanishing of `H¹(X, ℐ_i ⊗ 𝒫)` makes
`Γ(X, 𝒫) ⟶ Γ(Z, i^*𝒫)` surjective
(`Stacks.Cohomology.AmpleH1.epi_globalSections_map_unit_app`), so `t` lifts to a global `s`.
By [Stacks, Tag 0H78] the preimage of `X_s` is the nonvanishing locus of `t`, that is `{y}`; so
`X_s` meets `X ∖ U` nowhere, hence `X_s ⊆ U` and `X_s = U ⊓ X_s` is affine by
[Stacks, Tag 01PV]. The second half of the source's proof — that it is enough to do this at
closed points — is `isAmple_of_forall_isClosed_singleton`: the set of points that are served is
open, so its complement is closed in a quasi-compact Kolmogorov space and would contain a closed
point ([Stacks, Tag 005E], Mathlib's `IsClosed.exists_closed_singleton`), which is a
contradiction.

## Implementation notes

**The Stacks attribute for Tag 0B5P is withheld, and the reason is the hypothesis, not
the conclusion.** Clause (2) of Tag 0B5P quantifies over the *quasi-coherent sheaves of ideals*
`ℐ ⊆ 𝒪_X`; the hypothesis below quantifies over closed immersions `i : Z ⟶ X` and uses
`Stacks.ClosedImmersion.idealSheaf i`, the kernel of `𝒪_X ⟶ i_*𝒪_Z`. Every such kernel *is*
quasi-coherent — that is the instance `Stacks.Conormal.isQuasicoherent_idealSheaf`, which makes
the hypothesis below no stronger than the tag's — but the converse passage, from a
quasi-coherent ideal subsheaf of `𝒪_X` to the closed immersion it cuts out *together with an
identification of the two ideal sheaves*, is not in the library at the spelling the surjectivity
step consumes. So the statement below is not formally comparable with the tag, and the tag is
withheld. The one missing step is exactly that identification: for `I : X.IdealSheafData`, an
isomorphism of `𝒪_X`-submodules between `I` and
`Stacks.ClosedImmersion.idealSheaf I.subschemeι`.

**The reduced structure is Mathlib's.** The closed subscheme attached to `C` is
`(Scheme.IdealSheafData.vanishingIdeal ⟨C, _⟩).subscheme`, whose inclusion is a closed immersion
with image `C` by `Scheme.IdealSheafData.range_subschemeι` and
`Scheme.IdealSheafData.coe_support_vanishingIdeal`. Reducedness is not used; any closed
subscheme supported on `C` would do, which is why the per-point step takes the closed immersion
and the equation `Set.range i.base = (X ∖ U) ∪ {y}` as data.

**Both Tag 01CS invertibility classes appear.**
`AlgebraicGeometry.SheafOfModules.IsInvertible` is what the tensor powers of Tag 01CU and
`Scheme.Modules.IsAmple` are stated for; `Stacks.SheafOfModules.IsInvertible` is what the
nonvanishing locus of Tag 01CY, Tag 01PV and Tag 0B8L are stated for. They are carried across
by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, and the per-point step takes
both as binders rather than deriving one from the other inside, because instance search does not
cross between them.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 005E](https://stacks.math.columbia.edu/tag/005E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible
open RingedSpaceModuleAdjunction
-- (open removed: its only name was the merged moduleGlobalSections)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The section that the criterion for ampleness produces at a closed point.**

Let `𝒫` be an invertible `𝒪_X`-module, let `U` be an affine open of `X` containing a point `y`
whose singleton is closed, and let `i : Z ⟶ X` be a closed immersion whose image is
`(X ∖ U) ∪ {y}`. If `H¹(X, ℐ_i ⊗ 𝒫) = 0` then `𝒫` has a global section `s` with `y ∈ X_s` and
`X_s` affine.

The nonvanishing locus is forced into `U`: the preimage of `X_s` along `i` is the nonvanishing
locus of the section of `i^*𝒫` that was lifted, which was arranged to be `{y}`, so no point of
`X ∖ U` lies in `X_s`. -/
public theorem exists_sections_mem_isAffineOpen_nonvanishingOpen
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (P : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property P]
    [hP' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property P]
    (hzero : IsZero (((moduleGlobalSections X).rightDerived 1).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj (P)))))
    (U : X.Opens) (hUaff : IsAffineOpen U) (y : X) (hyU : y ∈ U)
    (hy : IsClosed ({y} : Set X))
    (hrange : Set.range i.base = (↑U : Set X)ᶜ ∪ {y}) :
    ∃ s : P.sections, y ∈ nonvanishingOpen (X := X.toRingedSpace) P s ∧
      IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) P s) := by
  have hinj : Function.Injective i.base := (IsClosedImmersion.isClosedEmbedding i).injective
  obtain ⟨y', hy'⟩ : ∃ z : Z, i.base z = y := by
    rw [← Set.mem_range, hrange]; exact Or.inr rfl
  have hpre_eq : ∀ S : Set X, (∀ z : Z, i.base z ∈ S ↔ i.base z = y) → i.base ⁻¹' S = {y'} := by
    intro S hS
    ext z
    rw [Set.mem_preimage, hS, Set.mem_singleton_iff, ← hy', hinj.eq_iff]
  have hy'closed : IsClosed ({y'} : Set Z) :=
    hpre_eq {y} (fun _ => Iff.rfl) ▸ hy.preimage i.base.hom.continuous
  have hy'open : IsOpen ({y'} : Set Z) := by
    refine hpre_eq U (fun z => ⟨fun h => ?_, fun h => h ▸ hyU⟩) ▸
      U.isOpen.preimage i.base.hom.continuous
    exact ((hrange ▸ Set.mem_range_self z : i.base z ∈ (↑U : Set X)ᶜ ∪ {y}).resolve_left
      (not_not.mpr h))
  have hpull : Stacks.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property
      ((modulePullback i.toLRSHom.toShHom).obj P) :=
    @Stacks.RingedSpace.isInvertible_modulePullback Z.toRingedSpace X.toRingedSpace
      i.toLRSHom.toShHom P hP'
  obtain ⟨t, ht⟩ := @Stacks.Cohomology.AmpleH1.exists_sections_nonvanishingLocus_eq_singleton
    Z ((modulePullback i.toLRSHom.toShHom).obj P) hpull y' hy'open hy'closed
  obtain ⟨s, hs⟩ := Stacks.Cohomology.AmpleH1.surjective_modulePullbackSection
    i P (Stacks.Cohomology.AmpleH1.epi_globalSections_map_unit_app i P hzero) t
  have hpre : i.base ⁻¹' (nonvanishingLocus (X := X.toRingedSpace) P s) = {y'} := by
    have h := Stacks.SheafOfModules.preimage_nonvanishingLocus i.toLRSHom P s
    rw [h, hs, ht]
  have hmem : ∀ w : Z, i.base w ∈ nonvanishingLocus (X := X.toRingedSpace) P s ↔ w = y' := by
    intro w
    rw [← Set.mem_preimage, hpre, Set.mem_singleton_iff]
  refine ⟨s, hy' ▸ (hmem y').2 rfl, ?_⟩
  · have hle : (nonvanishingOpen (X := X.toRingedSpace) P s : Set X) ⊆ (↑U : Set X) := by
      intro z hz
      by_contra hzU
      obtain ⟨w, hw⟩ : z ∈ Set.range i.base := by rw [hrange]; exact Or.inl hzU
      exact hzU (hw ▸ (hmem w).1 (hw ▸ hz) ▸ hy' ▸ hyU)
    have heq : U ⊓ nonvanishingOpen (X := X.toRingedSpace) P s
        = nonvanishingOpen (X := X.toRingedSpace) P s :=
      inf_eq_right.mpr hle
    exact heq ▸ isAffineOpen_inf_nonvanishingOpen P s U hUaff

/-- **Ampleness is detected at closed points.** On a quasi-compact scheme an invertible module
is ample as soon as every point whose singleton is closed lies in an affine nonvanishing locus
of a global section of some positive tensor power.

The set of points that are so served is open — a witness at a point serves every point of its
nonvanishing locus — so its complement is closed, and a nonempty closed subset of a
quasi-compact Kolmogorov space contains a point whose singleton is closed
([Stacks, Tag 005E]). -/
public theorem isAmple_of_forall_isClosed_singleton {X : Scheme.{u}} [CompactSpace X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        x ∈ nonvanishingOpen (X := X.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
          IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) :
    IsAmple X L := by
  refine ⟨‹_›, fun x => ?_⟩
  by_contra hx
  have hopen : IsOpen {z : X | ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        z ∈ nonvanishingOpen (X := X.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
          IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)} := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨n, hn, s, hzs, haff⟩
    exact ⟨(nonvanishingOpen (X := X.toRingedSpace) _ s : Set X),
      fun w hw => ⟨n, hn, s, hw, haff⟩,
      (nonvanishingOpen (X := X.toRingedSpace) _ s).isOpen, hzs⟩
  obtain ⟨y, hy, hyclosed⟩ := hopen.isClosed_compl.exists_closed_singleton ⟨x, hx⟩
  exact hy (h y hyclosed)

/-- **[Stacks, Tag 0B5P] with its hypothesis read over closed subschemes.** Let `X` be a
quasi-compact scheme and `𝓛` an invertible `𝒪_X`-module. If for every closed immersion
`i : Z ⟶ X` there is an `n ≥ 1` with `H¹(X, ℐ_i ⊗ 𝓛^{⊗ n}) = 0`, then `𝓛` is ample.

The tag is withheld: its clause (2) quantifies over quasi-coherent ideal subsheaves of `𝒪_X`,
and the passage from such a subsheaf to the ideal sheaf of its closed subscheme is not
available. See the implementation notes of this file. -/
public theorem isAmple_of_forall_exists_isZero_h1_idealSheaf {X : Scheme.{u}} [CompactSpace X]
    (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hvan : ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → ∃ n : ℕ, 1 ≤ n ∧
      IsZero (((moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
              ((tensorPower X.toRingedSpace.presheaf
                (structureSheafRing X.toRingedSpace).property L (n : ℤ))))))) :
    IsAmple X L := by
  refine isAmple_of_forall_isClosed_singleton L fun y hy => ?_
  obtain ⟨U, hUaff, hyU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ y ∈ U := by
    obtain ⟨U, hU, hyU, -⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top y)
    exact ⟨U, hU, hyU⟩
  have hC : IsClosed ((↑U : Set X)ᶜ ∪ {y}) := (U.isOpen.isClosed_compl).union hy
  obtain ⟨n, hn, hzero⟩ :=
    hvan (Scheme.IdealSheafData.vanishingIdeal ⟨(↑U : Set X)ᶜ ∪ {y}, hC⟩).subschemeι
      inferInstance
  refine ⟨n, hn, ?_⟩
  exact @exists_sections_mem_isAffineOpen_nonvanishingOpen X _
    (Scheme.IdealSheafData.vanishingIdeal ⟨(↑U : Set X)ᶜ ∪ {y}, hC⟩).subschemeι inferInstance
    (tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ))
    (tensorPower_isInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ))
    inferInstance hzero U hUaff y hyU hy
    (by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl)

end AlgebraicGeometry.Scheme.Modules

end
