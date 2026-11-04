module

public import StacksFrontier.AlgebraicGeometry.RelativeAmpleComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.LocalizedRestriction
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01VJ: relative ampleness is local on the base

Let `f : X ⟶ S` be a quasi-compact morphism of schemes and `L` an invertible `𝒪_X`-module. If
some affine open covering `S = ⋃ V_i` has every restriction `L|_{f⁻¹V_i}` ample, then `L` is
ample relative to `f` in the sense of [Stacks, Tag 01VH]: the restriction `L|_{f⁻¹V}` is ample
for **every** affine open `V ⊆ S`. The converse is immediate, so clauses (1) and (3) of
[Stacks, Tag 01VJ] are equivalent.

## Main results

* `Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple`:
  **Tag 01VJ, (3) implies (1)**.
* `Stacks.RelativeAmpleLocalOnBase.exists_affine_isAmple_cover_of_isRelativelyAmple` and
  `isRelativelyAmple_iff_exists_affine_isAmple_cover`: **Tag 01VJ, (1) implies (3)**, and the
  resulting equivalence.
* `Stacks.RelativeAmpleLocalOnBase.relativeAmpleLocalOnBase`:
  `Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase` is a theorem, so the results in
  that file carrying it as a hypothesis — and in particular [Stacks, Tag 0C4L] — are
  unconditional.
* `Stacks.RelativeAmpleLocalOnBase.isAmple_pullbackModule_iff`: ampleness of `L` on an open
  subscheme `A`, read as a statement about sections of the tensor powers of `L` over the open
  `A` of `X`.
* `Stacks.RelativeAmpleLocalOnBase.exists_section_nonvanishingLocusOn_eq`: a section over a
  basic open `X_g` of a qcqs open `Y` extends, after multiplication by a power of `g`, to a
  section over `Y` with exactly the same nonvanishing locus.
* `Stacks.RelativeAmpleLocalOnBase.isAmple_of_basicOpen_cover`: ampleness glues along a cover of
  a quasi-compact open by basic opens with ample pairwise intersections.
* `Stacks.RelativeAmpleLocalOnBase.quasiSeparatedSpace_of_isAmple`: a scheme carrying an ample
  invertible module is a quasi-separated space.
* `Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res` and `nonvanishingLocusOn_smul`: the
  two computations of the nonvanishing locus of a section over an open that the argument runs
  on.

## The route

No relative `Proj` is used. Fix an affine open `W ⊆ S` and a point `y ∈ f⁻¹W`. Choose a member
`V` of the given covering around `f(y)` and then, the basic opens of the affine `W` being a
basis, a function `c ∈ Γ(S, W)` with `f(y) ∈ S_c ⊆ W ⊓ V`. The preimage `f⁻¹(S_c)` is the basic
open of the pullback `g ∈ Γ(X, f⁻¹W)` of `c`, is quasi-compact because `f` is, and carries
an ample restriction of `L` by [Stacks, Tag 0B3E]. Ampleness there produces `n ≥ 1` and a section of
`L^{⊗ n}` over `X_g` whose nonvanishing locus is an affine open containing `y`. Multiplying by a
power of `g` turns that section into one over `f⁻¹W`
(`exists_section_nonvanishingLocusOn_eq`, which is the surjectivity half of [Stacks, Tag 01P7]
followed by one further multiplication by `g` to cut the nonvanishing locus back inside `X_g`),
with the *same* nonvanishing locus. So `f⁻¹W` is covered by affine nonvanishing opens of
sections of positive tensor powers of `L`, which is ampleness.

Quasi-separatedness of `f⁻¹W`, which [Stacks, Tag 01P7] needs, comes from the covering itself: a
scheme with an ample invertible module is quasi-separated (`quasiSeparatedSpace_of_isAmple`,
the first paragraph of the proof of [Stacks, Tag 01PY], here in the `Stacks.Ample` vocabulary),
the sets `X_g` cover `f⁻¹W`, and their pairwise intersections are again of the same form — the
basic open of a product — hence again ample. `isQuasiSeparated_of_affine_cover` assembles the
affine opens sitting inside them.

## Implementation notes

**Everything is read downstairs on `X`.** Ampleness of `L` on the open subscheme `A.toScheme`
speaks about global sections of the tensor powers of `A.ι^* L`, while the gluing argument needs
sections of the tensor powers of `L` itself over the open `A` of `X`.
`isAmple_pullbackModule_iff` performs that translation once: the powers cross the pullback by
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, the sections correspond by
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`, and the nonvanishing opens by
`Stacks.SectionPowerOpen.isAffineOpen_nonvanishingOpenOn_iff`.

The remaining clauses of [Stacks, Tag 01VJ] are proved elsewhere: clause (2) in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/RestrictBase.lean`, and clauses (4), (5), (6)
together with the whole equivalence (`Stacks.RelativeAmple.isRelativelyAmple_tfae`) in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/ProjCharacterization.lean`.

## References

* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [EGA II, Proposition 4.6.3]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn mem_nonvanishingLocusOn_iff
  nonvanishingLocusOn_subset)

universe u

namespace Stacks.NonvanishingLocusRestrict

variable {X : Scheme.{u}} (M : X.Modules)

/-- **Restriction of a section shrinks its nonvanishing locus by intersection.** For `V ≤ W` the
nonvanishing locus over `V` of the restriction of `m` is the part of the nonvanishing locus over
`W` that lies in `V`. -/
theorem nonvanishingLocusOn_res {V W : X.Opens} (h : V ≤ W) (m : Γ(M, W)) :
    nonvanishingLocusOn M V ((M.presheaf.map (homOfLE h).op).hom m) =
      (V : Set X) ∩ nonvanishingLocusOn M W m := by
  have key : ∀ (y : X) (hy : y ∈ V),
      (M.presheaf.germ V y hy).hom ((M.presheaf.map (homOfLE h).op).hom m) =
        (M.presheaf.germ W y (h hy)).hom m :=
    fun y hy => TopCat.Presheaf.germ_res_apply (C := Ab.{u}) M.presheaf (homOfLE h) y hy m
  refine Set.ext fun y => ⟨fun hy => ⟨hy.1, h hy.1, ?_⟩, fun hy => ⟨hy.1, ?_⟩⟩
  · exact fun hc => hy.2 ((key y hy.1).symm ▸ hc)
  · exact fun hc => hy.2.2 ((key y hy.1) ▸ hc)

/-- **Scaling a section by a function intersects its nonvanishing locus with a basic open**, over
an arbitrary open `V`. This is `Stacks.Ample.nonvanishingLocus_smul` for a section over `V`
rather than a global one. -/
theorem nonvanishingLocusOn_smul {V : X.Opens} (r : Γ(X, V)) (m : Γ(M, V)) :
    nonvanishingLocusOn M V (r • m) =
      (X.basicOpen r : Set X) ∩ nonvanishingLocusOn M V m := by
  refine Set.ext fun y => ⟨?_, ?_⟩
  · rintro ⟨hy, hg⟩
    rw [Stacks.ModuleStalk.germ_smul M y V hy r m,
      Stacks.ModuleStalk.smul_mem_maximalSmul_iff, not_or, not_not] at hg
    exact ⟨(X.mem_basicOpen r y hy).mpr hg.1, hy, hg.2⟩
  · rintro ⟨hb, hy, hg⟩
    refine ⟨hy, ?_⟩
    rw [Stacks.ModuleStalk.germ_smul M y V hy r m,
      Stacks.ModuleStalk.smul_mem_maximalSmul_iff, not_or, not_not]
    exact ⟨(X.mem_basicOpen r y hy).mp hb, hg⟩

end Stacks.NonvanishingLocusRestrict

namespace Stacks.RelativeAmpleLocalOnBase

/-! ### Quasi-separatedness from ampleness -/

/-- **A scheme carrying an ample invertible module is a quasi-separated space.** The affine
nonvanishing opens that ampleness produces cover `X` and meet each other in affine opens, by
[Stacks, Tag 01PV]. -/
theorem quasiSeparatedSpace_of_isAmple {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : QuasiSeparatedSpace X := by
  classical
  choose n hn s U hU hxU hUaff using hL.2
  refine Scheme.quasiSeparatedSpace_of_isOpenCover U
    (TopologicalSpace.IsOpenCover.mk
      (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩)) hUaff fun i j => ?_
  have haff := (Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (tensorPowModule X L ((n j : ℕ) : ℤ)) (s j) (hUaff i)).isCompact
  rw [Opens.coe_inf, Stacks.NonvanishingOpen.coe_nonvanishingOpen, ← hU j] at haff
  exact haff

/-- **An open covered by affine opens with quasi-compact pairwise intersections is
quasi-separated.** The open subscheme is covered by the preimages of the given affine opens under
its own open immersion, and both affineness and compactness transport across that immersion. -/
theorem isQuasiSeparated_of_affine_cover {X : Scheme.{u}} (Y : X.Opens) {ι : Type*}
    (A : ι → X.Opens) (hAaff : ∀ i, IsAffineOpen (A i)) (hAY : ∀ i, A i ≤ Y)
    (hcov : ∀ y ∈ Y, ∃ i, y ∈ A i)
    (hint : ∀ i j, IsCompact ((A i : Set X) ∩ (A j : Set X))) :
    IsQuasiSeparated (Y : Set X) := by
  have himg : ∀ i, Y.ι ''ᵁ (Y.ι ⁻¹ᵁ A i) = A i := by
    intro i
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hAY i)
  rw [isQuasiSeparated_iff_quasiSeparatedSpace _ Y.isOpen]
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (X := Y.toScheme) (fun i => Y.ι ⁻¹ᵁ A i)
    (TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun y _ => ?_))
    (fun i => (Y.ι.isAffineOpen_iff_of_isOpenImmersion).mp (by rw [himg i]; exact hAaff i))
    ?_
  · obtain ⟨i, hi⟩ := hcov (Y.ι.base y) y.2
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i j
    have hsub : ((Y.ι ⁻¹ᵁ A i : Y.toScheme.Opens) : Set Y.toScheme) ∩ (Y.ι ⁻¹ᵁ A j) =
        Y.ι.base ⁻¹' ((A i : Set X) ∩ (A j : Set X)) := rfl
    rw [hsub, Y.ι.isOpenEmbedding.isEmbedding.isCompact_iff,
      Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι,
      Set.inter_eq_self_of_subset_left (Set.inter_subset_left.trans (hAY i))]
    exact hint i j

/-- The intersection of an affine open with the basic open of a section of the structure sheaf
over a larger open is affine: it is a basic open of the affine. -/
theorem isAffineOpen_inf_basicOpen {X : Scheme.{u}} {A Y : X.Opens} (hA : IsAffineOpen A)
    (hAY : A ≤ Y) (g : Γ(X, Y)) : IsAffineOpen (A ⊓ X.basicOpen g) := by
  have h := hA.basicOpen (X.presheaf.map (homOfLE hAY).op g)
  rwa [Scheme.basicOpen_res] at h

/-! ### Ampleness on an open subscheme, read on the ambient scheme -/

section Translate

open Stacks.AmplePullbackPart1 (sectionOfRestrictGlobalSection)
open Stacks.NonvanishingLocusRestrict (restrictSection
  restrictSection_sectionOfRestrictGlobalSection mem_nonvanishingLocus_restrictSection_iff
  mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection)
open Stacks.SectionPowerOpen (nonvanishingOpenOn isAffineOpen_nonvanishingOpenOn_iff)

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (A : X.Opens)

/-- **Ampleness of the restriction of `L` to an open subscheme `A`, read as a statement about
sections over `A` of the tensor powers of `L` on `X`.** The tensor powers are moved across the
pullback by [Stacks, Tag 01CD] and the nonvanishing opens are compared by
`Stacks.SectionPowerOpen.isAffineOpen_nonvanishingOpenOn_iff`. -/
theorem isAmple_pullbackModule_iff :
    IsAmple A.toScheme (Stacks.AmpleLocallyClosed.pullbackModule A.ι L) ↔
      CompactSpace A.toScheme ∧ ∀ y ∈ A, ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : Γ(tensorPowModule X L (n : ℤ), A),
          IsAffineOpen (nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) A s) ∧
            y ∈ nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) A s := by
  refine Iff.trans (Iff.trans (isAmple_iff A.toScheme _)
    (Stacks.RelativeVeryAmple.isAmpleForPowers_congr_nat
      (pow' := fun m : ℤ => Stacks.AmpleLocallyClosed.pullbackModule A.ι (tensorPowModule X L m))
      fun n : ℕ => (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso A.ι L n).symm))
    (Iff.trans (isAmpleForPowers_iff A.toScheme _) ?_)
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h x => ?_⟩
  · obtain ⟨n, hn, t, U', hU', hyU', hU'aff⟩ := h ⟨y, hy⟩
    refine ⟨n, hn, sectionOfRestrictGlobalSection A (tensorPowModule X L (n : ℤ)) t, ?_, ?_⟩
    · rw [isAffineOpen_nonvanishingOpenOn_iff,
        restrictSection_sectionOfRestrictGlobalSection]
      have he : Stacks.NonvanishingOpen.nonvanishingOpen A.toScheme
          (Stacks.AmpleLocallyClosed.pullbackModule A.ι (tensorPowModule X L (n : ℤ))) t = U' :=
        Opens.ext (by rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, hU'])
      rw [he]
      exact hU'aff
    · refine (mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection A _ t ⟨y, hy⟩).mp ?_
      rw [← hU']
      exact hyU'
  · obtain ⟨n, hn, s, haff, hmem⟩ := h (A.ι.base x) x.2
    exact ⟨n, hn, restrictSection A _ s,
      Stacks.NonvanishingOpen.nonvanishingOpen A.toScheme _ _, rfl,
      (mem_nonvanishingLocus_restrictSection_iff A _ s x).mpr hmem,
      (isAffineOpen_nonvanishingOpenOn_iff _ A s).mp haff⟩

end Translate

/-! ### Extending a section from a basic open -/

section Extend

open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn nonvanishingLocusOn_subset
  nonvanishingLocusOn_res nonvanishingLocusOn_smul)

/-- Restricting a section to an open `V ≤ W` that contains its nonvanishing locus does not change
the nonvanishing locus. -/
private theorem nonvanishingLocusOn_res_of_subset {X : Scheme.{u}} (M : X.Modules) {V W : X.Opens}
    (h : V ≤ W) (m : Γ(M, W)) (hsub : nonvanishingLocusOn M W m ⊆ V) :
    nonvanishingLocusOn M V ((M.presheaf.map (homOfLE h).op).hom m) =
      nonvanishingLocusOn M W m := by
  rw [nonvanishingLocusOn_res M h m]
  exact Set.inter_eq_self_of_subset_right hsub

/-- **A section over a basic open of a qcqs open becomes, after multiplication by the function,
the restriction of a section with the same nonvanishing locus.** Multiplying the extension
supplied by [Stacks, Tag 01P7] by one further power of `g` cuts its nonvanishing locus back
inside `X_g`, where it agrees with that of the original section. -/
theorem exists_section_nonvanishingLocusOn_eq {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {Y : X.Opens} (hYcpt : IsCompact (Y : Set X))
    (hqs : IsQuasiSeparated (Y : Set X)) (g : Γ(X, Y)) (s : Γ(M, X.basicOpen g)) :
    ∃ u : Γ(M, Y), nonvanishingLocusOn M Y u = nonvanishingLocusOn M (X.basicOpen g) s := by
  have hboY : X.basicOpen g ≤ Y := X.basicOpen_le g
  have hZbo : Y ⊓ X.basicOpen g = X.basicOpen g := inf_eq_right.mpr hboY
  set s' : Γ(M, Y ⊓ X.basicOpen g) :=
    M.presheaf.map (homOfLE (inf_le_right : Y ⊓ X.basicOpen g ≤ X.basicOpen g)).op s
  obtain ⟨w, k, hk⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_res_eq_pow_smul_of_isCompact M g hqs Y hYcpt le_rfl s'
  set r : Γ(X, Y ⊓ X.basicOpen g) :=
    X.presheaf.map (homOfLE (inf_le_left : Y ⊓ X.basicOpen g ≤ Y)).op g with hr
  refine ⟨g • w, ?_⟩
  have hru : M.presheaf.map (homOfLE (inf_le_left : Y ⊓ X.basicOpen g ≤ Y)).op (g • w)
      = r ^ (k + 1) • s' := by
    rw [Scheme.Modules.map_smul M (homOfLE (inf_le_left : Y ⊓ X.basicOpen g ≤ Y)) g w, ← hr, hk,
      smul_smul, ← pow_succ']
  have hLu : nonvanishingLocusOn M Y (g • w)
      = (X.basicOpen g : Set X) ∩ nonvanishingLocusOn M Y w := nonvanishingLocusOn_smul M g w
  have hLusub : nonvanishingLocusOn M Y (g • w) ⊆ ((Y ⊓ X.basicOpen g : X.Opens) : Set X) := by
    rw [hLu]
    exact fun z hz => ⟨nonvanishingLocusOn_subset M Y w hz.2, hz.1⟩
  have hres : nonvanishingLocusOn M (Y ⊓ X.basicOpen g)
        (M.presheaf.map (homOfLE (inf_le_left : Y ⊓ X.basicOpen g ≤ Y)).op (g • w))
      = nonvanishingLocusOn M Y (g • w) := by
    exact nonvanishingLocusOn_res_of_subset M inf_le_left (g • w) hLusub
  have hbor : X.basicOpen r = Y ⊓ X.basicOpen g := by
    rw [hr, Scheme.basicOpen_res]
    exact inf_eq_left.mpr inf_le_right
  have hL2 : nonvanishingLocusOn M (Y ⊓ X.basicOpen g) (r ^ (k + 1) • s')
      = nonvanishingLocusOn M (Y ⊓ X.basicOpen g) s' := by
    rw [nonvanishingLocusOn_smul M (r ^ (k + 1)) s', X.basicOpen_pow r (Nat.succ_pos k), hbor]
    exact Set.inter_eq_self_of_subset_right (nonvanishingLocusOn_subset M _ s')
  have hsub : nonvanishingLocusOn M (X.basicOpen g) s ⊆
      ((Y ⊓ X.basicOpen g : X.Opens) : Set X) := by
    rw [hZbo]
    exact nonvanishingLocusOn_subset M (X.basicOpen g) s
  have hL3 : nonvanishingLocusOn M (Y ⊓ X.basicOpen g) s'
      = nonvanishingLocusOn M (X.basicOpen g) s := by
    exact nonvanishingLocusOn_res_of_subset M inf_le_right s hsub
  rw [← hres, hru, hL2, hL3]

end Extend

/-! ### Gluing ampleness along a cover by basic opens -/

section Glue

open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open Stacks.SectionPowerOpen (nonvanishingOpenOn)

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (Y : X.Opens)

/-- **Ampleness on a quasi-compact open glues along a cover by basic opens whose pairwise
intersections are again ample.** Each point lies in one of the basic opens, where ampleness
supplies an affine nonvanishing open of a section of a tensor power; that section is pushed out
to a section over `Y` with the same nonvanishing locus by
`Stacks.RelativeAmpleLocalOnBase.exists_section_nonvanishingLocusOn_eq`. -/
theorem isAmple_of_basicOpen_cover (hYc : CompactSpace Y.toScheme) {ι : Type*} (b : ι → Γ(X, Y))
    (hcov : ∀ y ∈ Y, ∃ i, y ∈ X.basicOpen (b i))
    (hample : ∀ i, IsAmple (X.basicOpen (b i)).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (X.basicOpen (b i)).ι L))
    (hample₂ : ∀ i j, IsAmple (X.basicOpen (b i) ⊓ X.basicOpen (b j)).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (X.basicOpen (b i) ⊓ X.basicOpen (b j)).ι L)) :
    IsAmple Y.toScheme (Stacks.AmpleLocallyClosed.pullbackModule Y.ι L) := by
  classical
  have hYcpt : IsCompact (Y : Set X) := by
    rw [isCompact_iff_compactSpace]
    exact hYc
  have hqs : IsQuasiSeparated (Y : Set X) := by
    refine isQuasiSeparated_of_affine_cover Y
      (ι := Σ i : ι, {A : X.Opens // IsAffineOpen A ∧ A ≤ X.basicOpen (b i)})
      (fun p => p.2.1) (fun p => p.2.2.1)
      (fun p => p.2.2.2.trans (X.basicOpen_le (b p.1))) ?_ ?_
    · intro y hy
      obtain ⟨i, hi⟩ := hcov y hy
      obtain ⟨-, ⟨A, hA, rfl⟩, hyA, hAB⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hi (X.basicOpen (b i)).isOpen
      exact ⟨⟨i, ⟨A, hA, hAB⟩⟩, hyA⟩
    · rintro ⟨i, A₁, hA₁, hA₁B⟩ ⟨j, A₂, hA₂, hA₂B⟩
      have h1 : IsAffineOpen (A₁ ⊓ X.basicOpen (b j)) :=
        isAffineOpen_inf_basicOpen hA₁ (hA₁B.trans (X.basicOpen_le (b i))) (b j)
      have h2 : IsAffineOpen (A₂ ⊓ X.basicOpen (b i)) :=
        isAffineOpen_inf_basicOpen hA₂ (hA₂B.trans (X.basicOpen_le (b j))) (b i)
      have hqs₂ : IsQuasiSeparated
          ((X.basicOpen (b i) ⊓ X.basicOpen (b j) : X.Opens) : Set X) := by
        rw [isQuasiSeparated_iff_quasiSeparatedSpace _
          (X.basicOpen (b i) ⊓ X.basicOpen (b j)).isOpen]
        exact quasiSeparatedSpace_of_isAmple _ (hample₂ i j)
      have heq : ((A₁ : X.Opens) : Set X) ∩ ((A₂ : X.Opens) : Set X) =
          ((A₁ ⊓ X.basicOpen (b j) : X.Opens) : Set X) ∩
            ((A₂ ⊓ X.basicOpen (b i) : X.Opens) : Set X) :=
        Set.ext fun z => ⟨fun hz => ⟨⟨hz.1, hA₂B hz.2⟩, hz.2, hA₁B hz.1⟩,
          fun hz => ⟨hz.1.1, hz.2.1⟩⟩
      rw [heq]
      exact hqs₂ _ _ (fun z hz => ⟨hA₁B hz.1, hz.2⟩) (A₁ ⊓ X.basicOpen (b j)).isOpen
        h1.isCompact (fun z hz => ⟨hz.2, hA₂B hz.1⟩) (A₂ ⊓ X.basicOpen (b i)).isOpen h2.isCompact
  rw [isAmple_pullbackModule_iff]
  refine ⟨hYc, fun y hy => ?_⟩
  obtain ⟨i, hyi⟩ := hcov y hy
  obtain ⟨n, hn, s, haff, hmem⟩ :=
    ((isAmple_pullbackModule_iff L (X.basicOpen (b i))).mp (hample i)).2 y hyi
  have : (tensorPowModule X L (n : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L (n : ℤ)
  obtain ⟨u, hu⟩ := exists_section_nonvanishingLocusOn_eq (tensorPowModule X L (n : ℤ))
    hYcpt hqs (b i) s
  refine ⟨n, hn, u, ?_, ?_⟩
  · have he : nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) Y u
        = nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) (X.basicOpen (b i)) s := Opens.ext hu
    rw [he]
    exact haff
  · change y ∈ nonvanishingLocusOn (tensorPowModule X L (n : ℤ)) Y u
    rw [hu]
    exact hmem

end Glue

/-! ### Stacks Tag 01VJ -/

/-- **Stacks Tag 01VJ, clause (3) implies clause (1).** Let `f : X ⟶ S` be a quasi-compact
morphism of schemes and `L` an invertible `𝒪_X`-module. If every point of `S` has an affine open
neighbourhood `V` with `L|_{f⁻¹V}` ample, then `L` is ample relative to `f`, that is, `L|_{f⁻¹V}`
is ample for *every* affine open `V ⊆ S`.

For an affine open `W ⊆ S` the preimage `f⁻¹W` is covered by the preimages of basic opens of `W`
lying inside members of the given covering, and on each of those the restriction of `L` is ample
by [Stacks, Tag 0B3E]; those preimages are the basic opens of the pullbacks to `f⁻¹W` of the
cutting functions, so
`Stacks.RelativeAmpleLocalOnBase.isAmple_of_basicOpen_cover` assembles them. -/
@[stacks 01VJ "(3) implies (1): relative ampleness may be checked on an affine open covering",
  ega "II 4.6.4" "Sufficiency",
  ega "II 8.10.6" "partial"]
theorem isRelativelyAmple_of_forall_exists_isAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (hcov : ∀ x : S, ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧
      IsAmple (f ⁻¹ᵁ V).toScheme (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L)) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  classical
  have := hf
  choose V hVaff hxV hVample using hcov
  refine ⟨hf, fun W hW => ?_⟩
  have hbasic : ∀ x : S, ∃ c : Γ(S, W), (x ∈ W → x ∈ S.basicOpen c) ∧ S.basicOpen c ≤ V x := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨c, hcV, hxc⟩ := hW.exists_basicOpen_le (⟨x, hxV x⟩ : V x) hx
      exact ⟨c, fun _ => hxc, hcV⟩
    · exact ⟨0, fun h => absurd h hx, by simp⟩
  choose c hcmem hcle using hbasic
  have hpre : ∀ r : Γ(S, W), X.basicOpen (f.app W r) = f ⁻¹ᵁ S.basicOpen r :=
    fun r => (f.preimage_basicOpen r).symm
  have hamp : ∀ (x : S) (r : Γ(S, W)), S.basicOpen r ≤ S.basicOpen (c x) →
      IsAmple (X.basicOpen (f.app W r)).toScheme
        (Stacks.AmpleLocallyClosed.pullbackModule (X.basicOpen (f.app W r)).ι L) := by
    intro x r hr
    refine Stacks.RelativeAmpleComposition.isAmple_restrict_of_le (Z := f ⁻¹ᵁ V x) ?_ L
      (hVample x) ?_
    · rw [hpre r]
      exact fun z hz => hcle x (hr hz)
    · have hc : IsCompact ((X.basicOpen (f.app W r) : X.Opens) : Set X) := by
        rw [hpre r]
        exact f.isCompact_preimage (hW.basicOpen r).isCompact
      rwa [isCompact_iff_compactSpace] at hc
  have hmul : ∀ x z : S, X.basicOpen (f.app W (c x)) ⊓ X.basicOpen (f.app W (c z))
      = X.basicOpen (f.app W (c x * c z)) := by
    intro x z
    rw [map_mul, Scheme.basicOpen_mul]
  refine isAmple_of_basicOpen_cover L (f ⁻¹ᵁ W)
    (Stacks.RelativeAmpleComposition.compactSpace_preimage_of_isCompact f W hW.isCompact)
    (fun x : S => f.app W (c x)) (fun y hy => ?_) (fun x => hamp x (c x) le_rfl) fun x z => ?_
  · refine ⟨f.base y, ?_⟩
    rw [hpre (c (f.base y))]
    exact hcmem (f.base y) hy
  · rw [hmul x z]
    refine hamp x (c x * c z) ?_
    rw [Scheme.basicOpen_mul]
    exact inf_le_left

/-- **Stacks Tag 01VJ, clause (1) implies clause (3).** A relatively ample module restricts to an
ample module on the preimage of *some* affine open neighbourhood of every point of the base,
because the affine opens of the base are a basis of its topology. -/
@[stacks 01VJ "(1) implies (3): the affine opens of the base are such a covering"]
theorem exists_affine_isAmple_cover_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (x : S) :
    ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧
      IsAmple (f ⁻¹ᵁ V).toScheme (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L) := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨V, hV, hxV, hL.2 V hV⟩

/-- **Stacks Tag 01VJ, clause (1) if and only if clause (3).** For a quasi-compact `f`, relative
ampleness of `L` is equivalent to ampleness of `L` on the preimage of each member of *some*
affine open covering of the base. -/
theorem isRelativelyAmple_iff_exists_affine_isAmple_cover {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f) :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔ ∀ x : S, ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧
      IsAmple (f ⁻¹ᵁ V).toScheme (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L) :=
  ⟨fun hL => exists_affine_isAmple_cover_of_isRelativelyAmple f L hL,
    isRelativelyAmple_of_forall_exists_isAmple f L hf⟩

/-- **`Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase` is a theorem**, so every result
in this repository carrying it as a hypothesis is unconditional. -/
@[ega "II 4.6.4" "Sufficiency"]
theorem relativeAmpleLocalOnBase :
    Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase.{u} := by
  intro X S f L inst hf hcov
  have := inst
  exact isRelativelyAmple_of_forall_exists_isAmple f L hf hcov

end Stacks.RelativeAmpleLocalOnBase

end
