module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.FiniteExistence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Reindex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometry of the induction on the affine stratification number

On a nonempty quasi-compact quasi-separated scheme `X` with affine stratification number `n`,
the cohomology `Hᵖ(X, F)` of a quasi-coherent `𝒪_X`-module vanishes for `p > n`. This file
supplies the geometry that the source's induction runs on, and assembles the induction from it;
the cohomological dévissage step is not proved here, so nothing in this file carries the tag of
that proposition.

## Main definitions

* `AlgebraicGeometry.QuasicoherentCohomologyVanishesAbove`: the vanishing predicate.
* `AlgebraicGeometry.AffineStratification.complement`: the reduced closed subscheme on the
  complement of the top stratum of an affine stratification indexed by `Fin (n + 1)`.

## Main results

* `AlgebraicGeometry.nonempty_affineStratification_affineStratificationNumber`: a quasi-compact
  quasi-separated scheme carries an affine stratification indexed by `Fin (n + 1)` for `n` its
  affine stratification number.
* `AlgebraicGeometry.AffineStratification.isOpen_strata_last`: the top stratum of an affine
  stratification indexed by `Fin (n + 1)` is open.
* `AlgebraicGeometry.AffineStratification.nonempty_complement`: the strata below the top one
  restrict to an affine stratification, one shorter, of the complement of the top stratum.
* `AlgebraicGeometry.isAffineHom_ι_of_isAffineHom_reducedInducedInclusion`: an open whose reduced
  induced scheme is affine with affine inclusion is an affine open with affine inclusion, granted
  [Stacks, Tag 06AD].
* `AlgebraicGeometry.quasicoherentCohomologyVanishesAbove_zero_of_isAffine`: the base case of the
  induction, Serre vanishing on an affine scheme.
* `AlgebraicGeometry.isZero_cohomology_of_affineStratificationNumber_lt_of_devissage`: the
  induction assembled from its two inputs. It is conditional and carries no tag.

## Implementation notes

Two inputs of the source's proof are hypotheses of the assembled induction rather than results.
[Stacks, Tag 06AD] — a scheme with an affine closed subscheme carrying the whole underlying space
is affine — has no formalization to call on; it reduces to [Stacks, Tag 05YU], affineness of the
target of a surjective universally closed morphism from an affine scheme, which is likewise
unavailable. The cohomological dévissage step is not carried out here. Everything else is proved:
the extraction of an optimal stratification, the openness and affineness of the top stratum, the
affineness of its inclusion, and the stratification of its closed complement.

## References

* [Stacks Project, Tag 0F2Y](https://stacks.math.columbia.edu/tag/0F2Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u v

namespace AlgebraicGeometry

/-- `Hᵖ(X, F) = 0` for every quasi-coherent `𝒪_X`-module `F` and every `p > n`. -/
def QuasicoherentCohomologyVanishesAbove (X : Scheme.{u}) (n : ℕ) : Prop :=
  ∀ F : X.Modules, F.IsQuasicoherent → ∀ p : ℕ, n < p →
    IsZero (Hgroup X.ringCatSheaf ⊤ p F)

/-- On an affine scheme the cohomology of a quasi-coherent module vanishes in positive degrees,
which is the vanishing above the affine stratification number zero. -/
@[ega "II 5.2.4"]
theorem quasicoherentCohomologyVanishesAbove_zero_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    QuasicoherentCohomologyVanishesAbove X 0 := by
  intro F _ p hp
  exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊤ (isAffineOpen_top X) p hp

/-! ### The length of a finite nonempty poset -/

/-- A nonempty finite preorder has a largest `<`-chain. -/
private theorem finiteDimensionalOrder_of_finite (I : Type v) [Preorder I] [Finite I]
    [Nonempty I] : FiniteDimensionalOrder I := by
  classical
  have : Fintype I := Fintype.ofFinite I
  refine not_infiniteDimensionalOrder_iff.mp fun hinf => ?_
  have h := (LTSeries.withLength I (Fintype.card I)).length_lt_card
  rw [LTSeries.length_withLength] at h
  exact lt_irrefl _ h

/-- The Krull dimension of a nonempty finite poset is a natural number. -/
private theorem exists_krullDim_eq_natCast (I : Type v) [PartialOrder I] [Finite I]
    [Nonempty I] : ∃ n : ℕ, Order.krullDim I = n := by
  have : FiniteDimensionalOrder I := finiteDimensionalOrder_of_finite I
  exact ⟨_, Order.krullDim_eq_length_of_finiteDimensionalOrder⟩

/-! ### Extracting the optimal stratification -/

/-- A quasi-compact quasi-separated scheme carries an affine stratification indexed by
`Fin (n + 1)` for `n` its affine stratification number: a finite affine stratification exists by
[Stacks, Tag 0F2U], is reindexed by an interval by [Stacks, Tag 0F2T], and the infimum defining
the affine stratification number is therefore attained. -/
theorem nonempty_affineStratification_affineStratificationNumber (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (AffineStratification X (Fin (affineStratificationNumber X + 1))) := by
  classical
  refine Nat.sInf_mem (s := {n : ℕ | Nonempty (AffineStratification X (Fin (n + 1)))}) ?_
  obtain ⟨I, hI, order, ⟨s⟩⟩ :=
    (hasFiniteAffineStratification_iff.{u, u} X).2 ⟨inferInstance, inferInstance⟩
  let _ : PartialOrder I := order
  by_cases hne : Nonempty I
  · obtain ⟨n, hn⟩ := exists_krullDim_eq_natCast I
    exact ⟨n, exists_affineStratification_fin s n (Or.inl hn)⟩
  · exact ⟨0, exists_affineStratification_fin s 0 (Or.inr ⟨not_nonempty_iff.mp hne, rfl⟩)⟩

/-! ### The top stratum -/

/-- A stratum of an affine stratification is the complement of the union of the strata below an
index `i`, as soon as the indices below `i` are exactly the indices other than the given one:
the strata are pairwise disjoint and cover the space. -/
theorem AffineStratification.strata_eq_compl_biUnion_le {X : Scheme.{u}} {I : Type v}
    [PartialOrder I] (s : AffineStratification X I) (i k : I) (h : ∀ j, j ≤ i ↔ j ≠ k) :
    s.strata k = (⋃ j ∈ {j | j ≤ i}, s.strata j)ᶜ := by
  have hpart := s.isLocallyFiniteStratification.isStratification.isPartition
  ext x
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
  refine ⟨fun hx j hj hxj => (hpart.disjoint j k ((h j).1 hj)).le_bot ⟨hxj, hx⟩, fun hx => ?_⟩
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hpart.cover ▸ Set.mem_univ x)
  obtain rfl | hjk := eq_or_ne j k
  · exact hxj
  · exact absurd hxj (hx j ((h j).2 hjk))

/-- The top stratum of an affine stratification indexed by `Fin (n + 1)` is open: it is the
complement of the union of the strata below it, which is closed because the family of strata is
a locally finite stratification. -/
theorem AffineStratification.isOpen_strata_last {X : Scheme.{u}} {n : ℕ}
    (s : AffineStratification X (Fin (n + 1))) : IsOpen (s.strata (Fin.last n)) := by
  classical
  rcases n with _ | m
  · have hcover := s.isLocallyFiniteStratification.isStratification.isPartition.cover
    have hsub : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have htop : s.strata (Fin.last 0) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
      exact (Subsingleton.elim j (Fin.last 0)) ▸ hxj
    rw [htop]
    exact isOpen_univ
  · have hle : ∀ j : Fin (m + 1 + 1), j ≤ (Fin.last m).castSucc ↔ j ≠ Fin.last (m + 1) := by
      intro j
      have hj := Fin.le_last j
      rw [Fin.le_def] at hj
      simp only [Fin.val_last] at hj
      rw [Fin.le_def]
      simp only [Fin.val_castSucc, Fin.val_last, ne_eq, Fin.ext_iff]
      omega
    rw [s.strata_eq_compl_biUnion_le ((Fin.last m).castSucc) (Fin.last (m + 1)) hle]
    exact (((closedZ_of_locallyFiniteStratification s.isLocallyFiniteStratification
      (fun i => ⋃ j ∈ {j | j ≤ i}, s.strata j) (fun _ => rfl)).1
      ((Fin.last m).castSucc))).isOpen_compl

/-! ### Peeling off the top stratum -/

/-- The complement of the top stratum of an affine stratification indexed by `Fin (n + 1)`, a
closed subset of `X`. -/
def AffineStratification.topComplement {X : Scheme.{u}} {n : ℕ}
    (s : AffineStratification X (Fin (n + 1))) : Closeds X :=
  ⟨(s.strata (Fin.last n))ᶜ, s.isOpen_strata_last.isClosed_compl⟩

/-- The reduced closed subscheme of `X` on the complement of the top stratum of an affine
stratification indexed by `Fin (n + 1)`. -/
noncomputable abbrev AffineStratification.complement {X : Scheme.{u}} {n : ℕ}
    (s : AffineStratification X (Fin (n + 1))) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal s.topComplement).subscheme

/-- The closed immersion of the complement of the top stratum into `X`. -/
noncomputable abbrev AffineStratification.complementι {X : Scheme.{u}} {n : ℕ}
    (s : AffineStratification X (Fin (n + 1))) : s.complement ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal s.topComplement).subschemeι

/-- The range of the closed immersion `complementι` is the complement of the top stratum. -/
theorem AffineStratification.range_complementι {X : Scheme.{u}} {n : ℕ}
    (s : AffineStratification X (Fin (n + 1))) :
    Set.range s.complementι = (s.strata (Fin.last n))ᶜ :=
  Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _

/-- For `j : Fin (m + 1 + 1)`, `j ≤ (Fin.last m).castSucc` if and only if
`j ≠ Fin.last (m + 1)`. -/
private theorem fin_le_castSucc_last_iff (m : ℕ) (j : Fin (m + 1 + 1)) :
    j ≤ (Fin.last m).castSucc ↔ j ≠ Fin.last (m + 1) := by
  have hj := Fin.le_last j
  rw [Fin.le_def] at hj
  simp only [Fin.val_last] at hj
  rw [Fin.le_def]
  simp only [Fin.val_castSucc, Fin.val_last, ne_eq, Fin.ext_iff]
  omega

/-- **Peeling off the top stratum.** The strata below the top one of an affine stratification of
`X` indexed by `Fin (m + 2)` restrict to an affine stratification, indexed by `Fin (m + 1)`, of
the reduced closed subscheme on the complement of the top stratum.

This is the geometric half of the induction of [Stacks, Tag 0F2Y]: the top stratum is an open
whose reduced induced scheme is affine with affine inclusion, and its closed complement carries a
stratification one shorter. -/
theorem AffineStratification.nonempty_complement {X : Scheme.{u}} {m : ℕ}
    (s : AffineStratification X (Fin (m + 2))) :
    Nonempty (AffineStratification s.complement (Fin (m + 1))) := by
  classical
  have hpart := s.isLocallyFiniteStratification.isStratification.isPartition
  set g := s.complementι with hgdef
  have hginj : Function.Injective g.base := g.isClosedEmbedding.injective
  have hgrange : Set.range g = (s.strata (Fin.last (m + 1)))ᶜ := s.range_complementι
  set T : Fin (m + 1) → Set s.complement := fun i => g ⁻¹' s.strata i.castSucc with hTdef
  have hcover : (⋃ i, T i) = Set.univ := by
    rw [hTdef, ← Set.preimage_iUnion, Set.preimage_eq_univ_iff, hgrange,
      s.strata_eq_compl_biUnion_le ((Fin.last m).castSucc) (Fin.last (m + 1))
        (fin_le_castSucc_last_iff m), compl_compl]
    refine Set.iUnion₂_subset fun j hj => ?_
    have hjne : j ≠ Fin.last (m + 1) := (fin_le_castSucc_last_iff m j).1 hj
    exact Set.subset_iUnion_of_subset (j.castPred hjne) (by rw [Fin.castSucc_castPred])
  have hlf : IsLocallyFiniteStratification T := by
    refine ⟨⟨⟨fun i => (hpart.locallyClosed i.castSucc).preimage g.continuous,
      fun i j hij => ?_, hcover⟩, fun i => ?_⟩, locallyFinite_of_finite _⟩
    · exact (hpart.disjoint i.castSucc j.castSucc
        fun hc => hij (Fin.castSucc_injective _ hc)).preimage _
    · intro y hy
      have h1 : g y ∈ closure (s.strata i.castSucc) :=
        g.continuous.closure_preimage_subset (s.strata i.castSucc) hy
      have h2 := s.isLocallyFiniteStratification.isStratification.closure_subset i.castSucc h1
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h2 ⊢
      obtain ⟨j, hji, hgj⟩ := h2
      have hjne : j ≠ Fin.last (m + 1) := (hji.trans_lt (Fin.castSucc_lt_last i)).ne
      refine ⟨j.castPred hjne, ?_, ?_⟩
      · rw [Fin.le_def] at hji ⊢
        simpa only [Fin.val_castSucc, Fin.coe_castPred] using hji
      · change g y ∈ s.strata ((j.castPred hjne).castSucc)
        rw [Fin.castSucc_castPred]
        exact hgj
  have hAff : ∀ i : Fin (m + 1),
      IsAffine (reducedInducedScheme (T i) (hlf.isStratification.isPartition.locallyClosed i)) ∧
        IsAffineHom
          (reducedInducedInclusion (T i) (hlf.isStratification.isPartition.locallyClosed i)) := by
    intro i
    have hTX := hpart.locallyClosed i.castSucc
    have : IsAffine (reducedInducedScheme (s.strata i.castSucc) hTX) := s.isAffine i.castSucc
    have : IsAffineHom (reducedInducedInclusion (s.strata i.castSucc) hTX) :=
      s.isAffineHom i.castSucc
    set J := Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds (reducedInducedScheme (s.strata i.castSucc) hTX)) with hJdef
    have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
    set f := J.subschemeι ≫ reducedInducedInclusion (s.strata i.castSucc) hTX with hfdef
    have hfrange : Set.range f = s.strata i.castSucc := by
      change Set.range ((reducedInducedInclusion (s.strata i.castSucc) hTX).base ∘
        J.subschemeι.base) = _
      rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      simpa using range_reducedInducedInclusion (s.strata i.castSucc) hTX
    have : IsImmersion f := inferInstance
    have : IsAffineHom f := inferInstance
    have hsub : Set.range f ⊆
        ((Scheme.IdealSheafData.vanishingIdeal s.topComplement).support : Set X) := by
      have hine : i.castSucc ≠ Fin.last (m + 1) := (Fin.castSucc_lt_last i).ne
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hfrange]
      intro x hx
      exact Set.mem_compl fun hxlast =>
        (hpart.disjoint i.castSucc (Fin.last (m + 1)) hine).le_bot ⟨hx, hxlast⟩
    obtain ⟨h, hh⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
      (Scheme.IdealSheafData.vanishingIdeal s.topComplement) f).2 hsub
    have hcomp : ∀ z, g (h z) = f z := fun z => by
      simpa only [← Scheme.Hom.comp_apply] using congrArg (fun k => k z) hh
    have : IsImmersion (h ≫ g) := by rw [hgdef, hh]; infer_instance
    have : IsImmersion h := IsImmersion.of_comp h g
    have : IsAffineHom h := by
      refine isAffineHom_of_forall_exists_isAffineOpen h fun y => ?_
      obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g y)) isOpen_univ
      refine ⟨g ⁻¹ᵁ (V : X.Opens), hyV, hV.preimage g, ?_⟩
      have hpre : h ⁻¹ᵁ (g ⁻¹ᵁ (V : X.Opens)) = f ⁻¹ᵁ (V : X.Opens) := by
        rw [← Scheme.Hom.comp_preimage, hgdef, hh]
      rw [hpre]
      exact hV.preimage f
    have hhrange : Set.range h = T i := by
      refine Set.eq_of_subset_of_subset ?_ ?_
      · rintro y ⟨z, rfl⟩
        change g (h z) ∈ s.strata i.castSucc
        rw [hcomp z]
        exact hfrange.le ⟨z, rfl⟩
      · intro y hy
        obtain ⟨z, hz⟩ := hfrange.ge hy
        exact ⟨z, hginj (by rw [hcomp z, hz])⟩
    exact isAffine_reducedInduced_of_range_eq (T i)
      (hlf.isStratification.isPartition.locallyClosed i) h hhrange
  exact ⟨{ strata := T
           isLocallyFiniteStratification := hlf
           isAffine := fun i => (hAff i).1
           isAffineHom := fun i => (hAff i).2 }⟩

/-! ### Affineness of an open with affine reduced induced structure -/

/-- The hypothesis of [Stacks, Tag 06AD]: a scheme admitting a surjective immersion from an
affine scheme is affine. A surjective immersion is a surjective closed immersion, so this is
exactly the source's statement that a scheme with an affine closed subscheme carrying the whole
underlying space is affine. -/
def IsAffineOfSurjectiveImmersion : Prop :=
  ∀ (Y Z : Scheme.{u}) (g : Z ⟶ Y), IsImmersion g → Set.range g.base = Set.univ →
    IsAffine Z → IsAffine Y

/-- An open subset whose reduced induced scheme is affine is an affine open, granted
[Stacks, Tag 06AD]: the reduced induced scheme on `U` factors through `U` as a surjective
immersion. -/
theorem isAffineOpen_of_isAffine_reducedInduced (haffine : IsAffineOfSurjectiveImmersion.{u})
    {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffine (reducedInducedScheme (U : Set X) U.isOpen.isLocallyClosed)) :
    IsAffineOpen U := by
  have hιinj : Function.Injective U.ι.base := (IsPreimmersion.isEmbedding U.ι).injective
  have hrange : Set.range (reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed).base =
      (U : Set X) := range_reducedInducedInclusion _ _
  have hsub : Set.range (reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed).base ≤
      Set.range U.ι.base := by
    rw [hrange, Scheme.Opens.range_ι]
  set L := IsOpenImmersion.lift U.ι
    (reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed) hsub with hLdef
  have hL : L ≫ U.ι = reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed :=
    IsOpenImmersion.lift_fac _ _ _
  have hLcomp : ∀ z, U.ι (L z) =
      reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed z := fun z => by
    simpa only [← Scheme.Hom.comp_apply] using congrArg (fun k => k z) hL
  have : IsImmersion (L ≫ U.ι) := by rw [hL]; infer_instance
  have : IsImmersion L := IsImmersion.of_comp L U.ι
  have hLrange : Set.range L.base = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨z, hz⟩ := hrange.ge ((Scheme.Opens.range_ι U).le ⟨y, rfl⟩)
    exact ⟨z, hιinj (by rw [hLcomp z, hz])⟩
  exact haffine U.toScheme _ L inferInstance hLrange hU

/-- An open subset whose reduced induced scheme is affine with affine inclusion is an affine open
whose own inclusion is an affine morphism, granted [Stacks, Tag 06AD]: the reduced induced scheme
on the intersection of `U` with an affine open `V` of `X` receives an affine immersion from the
affine open `V` of the reduced induced scheme on `U`, so `U ⊓ V` is affine. -/
theorem isAffineHom_ι_of_isAffineHom_reducedInducedInclusion
    (haffine : IsAffineOfSurjectiveImmersion.{u}) {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffine (reducedInducedScheme (U : Set X) U.isOpen.isLocallyClosed))
    (hUhom : IsAffineHom (reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed)) :
    IsAffineHom U.ι := by
  classical
  set incl := reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed with hinclDef
  refine isAffineHom_of_forall_exists_isAffineOpen U.ι fun x => ?_
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have : IsAffine (incl ⁻¹ᵁ (V : X.Opens)).toScheme := hV.preimage incl
  set k := (incl ⁻¹ᵁ (V : X.Opens)).ι ≫ incl with hkDef
  have : IsImmersion k := inferInstance
  have : IsAffineHom k := inferInstance
  have hkrange : Set.range k.base = ((U ⊓ (V : X.Opens) : X.Opens) : Set X) := by
    change Set.range (incl.base ∘ ((incl ⁻¹ᵁ (V : X.Opens)).ι).base) = _
    rw [Set.range_comp, Scheme.Opens.range_ι]
    change incl '' (incl ⁻¹' (V : Set X)) = _
    rw [Set.image_preimage_eq_inter_range, range_reducedInducedInclusion, Opens.coe_inf]
    exact Set.inter_comm _ _
  have hUV : IsAffineOpen (U ⊓ (V : X.Opens)) :=
    isAffineOpen_of_isAffine_reducedInduced haffine _
      (isAffine_reducedInduced_of_range_eq ((U ⊓ (V : X.Opens) : X.Opens) : Set X)
        (U ⊓ (V : X.Opens)).isOpen.isLocallyClosed k hkrange).1
  refine ⟨(V : X.Opens), hxV, hV, ?_⟩
  have heq : U.ι ⁻¹ᵁ (V : X.Opens) = U.ι ⁻¹ᵁ (U ⊓ (V : X.Opens)) := by
    ext y
    exact ⟨fun hy => ⟨y.2, hy⟩, fun hy => hy.2⟩
  rw [heq]
  exact hUV.preimage_of_isOpenImmersion U.ι fun y hy => ⟨⟨y, hy.1⟩, rfl⟩

/-! ### The vanishing -/

/-- The induction of [Stacks, Tag 0F2Y] assembled from its two inputs: on a nonempty
quasi-compact quasi-separated scheme `X` with affine stratification number `n` the cohomology
`Hᵖ(X, F)` of a quasi-coherent `𝒪_X`-module vanishes for `p > n`, given `haffine` and
`hdevissage`.

This is **not** a formalization of [Stacks, Tag 0F2Y] and carries no tag: `hdevissage` is the
inductive step of the proposition itself. What is proved here is the geometry the induction runs
on — a quasi-compact quasi-separated scheme carries an affine stratification indexed by
`Fin (n + 1)`, its top stratum is an open `U` which is affine with affine inclusion, and the
reduced closed subscheme on the complement of `U` carries an affine stratification indexed by
`Fin n` — together with the base case, the Serre vanishing of [Stacks, Tag 01XB] on an affine
scheme.

`haffine` is [Stacks, Tag 06AD]: a scheme admitting a surjective immersion from an affine scheme
is affine. It is what turns the affineness of the reduced induced scheme on a stratum, which is
what an affine stratification records, into affineness of the stratum itself. `hdevissage` is the
cohomological step of the source's proof, from the peeled geometry: the four-term exact sequence
`0 → K → F → j_*(F|_U) → Q → 0` for `j : U → X`, the vanishing of `Hᵖ(X, j_*(F|_U))` for `p > 0`
([Stacks, Tags 089W and 01XC]), the presentation of `K` and `Q` as filtered colimits of their
finite-type quasi-coherent submodules ([Stacks, Tag 01PG]) over which cohomology commutes
([Stacks, Tag 01FF]), and the scheme-theoretic support ([Stacks, Tag 056H]) of such a submodule,
a closed subscheme with the same underlying space as the complement of the top stratum and hence
with an affine stratification of the same length. -/
theorem isZero_cohomology_of_affineStratificationNumber_lt_of_devissage
    (haffine : IsAffineOfSurjectiveImmersion.{u})
    (hdevissage : ∀ (m : ℕ) (Y : Scheme.{u}) (U : Y.Opens), IsAffineOpen U → IsAffineHom U.ι →
      ∀ (V : Scheme.{u}) (j : V ⟶ Y), IsClosedImmersion j →
        Set.range j.base = (U : Set Y)ᶜ →
        Nonempty (AffineStratification V (Fin (m + 1))) →
        (∀ W : Scheme.{u}, Nonempty (AffineStratification W (Fin (m + 1))) →
          QuasicoherentCohomologyVanishesAbove W m) →
        QuasicoherentCohomologyVanishesAbove Y (m + 1))
    (X : Scheme.{u}) [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : affineStratificationNumber X < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  have key : ∀ (n : ℕ) (Y : Scheme.{u}), Nonempty (AffineStratification Y (Fin (n + 1))) →
      QuasicoherentCohomologyVanishesAbove Y n := by
    intro n
    induction n with
    | zero =>
      rintro Y ⟨t⟩
      have hLC := t.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed 0
      have hsub : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
      have hrange : Set.range (reducedInducedInclusion (t.strata 0) hLC).base = Set.univ := by
        refine (range_reducedInducedInclusion (t.strata 0) hLC).trans ?_
        refine Set.eq_univ_of_forall fun x => ?_
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp
          (t.isLocallyFiniteStratification.isStratification.isPartition.cover ▸ Set.mem_univ x)
        exact (Subsingleton.elim j 0) ▸ hxj
      have : IsAffine (reducedInducedScheme (t.strata 0) hLC) := t.isAffine 0
      have : IsAffine Y :=
        haffine Y _ (reducedInducedInclusion (t.strata 0) hLC) inferInstance hrange inferInstance
      exact quasicoherentCohomologyVanishesAbove_zero_of_isAffine Y
    | succ m ih =>
      rintro Y ⟨t⟩
      set U : Y.Opens := ⟨t.strata (Fin.last (m + 1)), t.isOpen_strata_last⟩ with hUdef
      have hUred : IsAffine (reducedInducedScheme (U : Set Y) U.isOpen.isLocallyClosed) :=
        t.isAffine (Fin.last (m + 1))
      have hUredHom :
          IsAffineHom (reducedInducedInclusion (U : Set Y) U.isOpen.isLocallyClosed) :=
        t.isAffineHom (Fin.last (m + 1))
      exact hdevissage m Y U (isAffineOpen_of_isAffine_reducedInduced haffine U hUred)
        (isAffineHom_ι_of_isAffineHom_reducedInducedInclusion haffine U hUred hUredHom)
        t.complement t.complementι inferInstance t.range_complementι t.nonempty_complement ih
  exact key (affineStratificationNumber X) X
    (nonempty_affineStratification_affineStratificationNumber X) F inferInstance p hp

end AlgebraicGeometry

end
