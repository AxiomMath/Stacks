module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Order.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.ReducedInduced
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Reindexing a finite affine stratification by an interval

A finite affine stratification of a scheme can be replaced by an affine stratification indexed
by `Fin (n + 1)`, where `n` is the length of the original index poset. The new strata are the
unions of the old strata of a fixed *level*, the level of `i` being `n - coheight i`; collecting
the strata of one level preserves local closedness, the stratification condition, and affineness
of both the stratum and its inclusion.

## Main results

* `AlgebraicGeometry.exists_affineStratification_fin`: a finite affine stratification yields one
  indexed by `Fin (n + 1)`, where `n` is the length of its index poset.

## Implementation notes

For a nonempty finite poset the length `n` is expressed as `Order.krullDim I = n`. The empty
poset has length zero in the source's natural-number convention, whereas its Krull dimension is
`⊥`; the second alternative of the hypothesis covers that case explicitly.

Two strata of the same level are incomparable, hence each is disjoint from the closure of the
other. That makes a level set locally closed — it is the intersection of the union of the
closures of its strata with an open set separating them — and makes the reduced induced scheme
on it a *disjoint* union of the reduced induced schemes on its strata. Affineness of a finite
disjoint union of affine opens (`AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint`) then gives
both conclusions.

The lift of a stratum into the level stratum containing it is a closed immersion with open
image, hence an isomorphism onto an open subscheme; that step uses reducedness of the reduced
induced scheme structure and the factorization criterion for maps out of a reduced scheme into a
closed subscheme.

## References

* [Stacks Project, Tag 0F2T](https://stacks.math.columbia.edu/tag/0F2T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u v

namespace AlgebraicGeometry

/-- The level of an index in a poset of length `n`: the number of steps from the top. -/
private noncomputable def stratumLevel {I : Type v} [PartialOrder I]
    (n : ℕ) (i : I) : Fin (n + 1) :=
  ⟨n - (Order.coheight i).toNat, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

private lemma coheight_le_nat {I : Type v} [PartialOrder I] [Finite I]
    {n : ℕ} (hn : Order.krullDim I = n) (i : I) :
    Order.coheight i ≤ n := by
  have h : (Order.coheight i : WithBot ℕ∞) ≤ n := by
    rw [← hn]
    exact Order.coheight_le_krullDim i
  exact WithBot.coe_le_coe.mp h

private lemma stratumLevel_mono {I : Type v} [PartialOrder I] [Finite I]
    {n : ℕ} (hn : Order.krullDim I = n) {i j : I} (hij : i ≤ j) :
    stratumLevel n i ≤ stratumLevel n j := by
  have hi := coheight_le_nat hn i
  have hc : Order.coheight j ≤ Order.coheight i := by
    change Order.height (OrderDual.toDual j) ≤ Order.height (OrderDual.toDual i)
    exact Order.height_mono hij
  have hci : Order.coheight i ≠ ⊤ := fun htop => by simp [htop] at hi
  have hnat : (Order.coheight j).toNat ≤ (Order.coheight i).toNat :=
    ENat.toNat_le_toNat hc hci
  simp only [stratumLevel, Fin.mk_le_mk]
  exact Nat.sub_le_sub_left hnat n

private lemma stratumLevel_strictMono {I : Type v} [PartialOrder I] [Finite I]
    {n : ℕ} (hn : Order.krullDim I = n) {i j : I} (hij : i < j) :
    stratumLevel n i < stratumLevel n j := by
  have hi := coheight_le_nat hn i
  have hj := coheight_le_nat hn j
  have htopi : Order.coheight i ≠ ⊤ := fun htop => by simp [htop] at hi
  have htopj : Order.coheight j ≠ ⊤ := fun htop => by simp [htop] at hj
  have hco := Order.coheight_add_one_le hij
  have hstrict : Order.coheight j < Order.coheight i :=
    ((ENat.lt_add_one_iff htopj).2 le_rfl).trans_le hco
  have hnat : (Order.coheight j).toNat < (Order.coheight i).toNat := by
    have h' : ((Order.coheight j).toNat : ℕ∞) < (Order.coheight i).toNat := by
      simpa only [ENat.natCast_toNat htopj, ENat.natCast_toNat htopi] using hstrict
    exact ENat.natCast_lt_natCast.mp h'
  have hiNat : (Order.coheight i).toNat ≤ n := ENat.toNat_le_of_le_natCast hi
  have hjNat : (Order.coheight j).toNat ≤ n := ENat.toNat_le_of_le_natCast hj
  simp only [stratumLevel, Fin.mk_lt_mk]
  omega

/-- The union of the strata of a fixed level. -/
private def levelStrata {X : Scheme.{u}} {I : Type v} [PartialOrder I]
    [Finite I] (n : ℕ) (s : AffineStratification X I) :
    Fin (n + 1) → Set X := fun k =>
      ⋃ i : {i : I // stratumLevel n i = k}, s.strata i.1

/-- Two strata containing a common point have the same index. -/
private lemma eq_of_mem_strata {X : Scheme.{u}} {I : Type v} [PartialOrder I]
    (s : AffineStratification X I) {x : X} {i j : I}
    (hi : x ∈ s.strata i) (hj : x ∈ s.strata j) : i = j := by
  by_contra h
  exact (s.isLocallyFiniteStratification.isStratification.isPartition.disjoint i j h).le_bot
    ⟨hi, hj⟩

/-- Every point lies in some stratum. -/
private lemma exists_mem_strata {X : Scheme.{u}} {I : Type v} [PartialOrder I]
    (s : AffineStratification X I) (x : X) : ∃ i, x ∈ s.strata i := by
  have hx : x ∈ ⋃ i, s.strata i := by
    rw [s.isLocallyFiniteStratification.isStratification.isPartition.cover]
    simp
  exact Set.mem_iUnion.mp hx

/-- A point in the closure of a stratum lies in a stratum of smaller or equal index. -/
private lemma exists_le_mem_strata_of_mem_closure {X : Scheme.{u}} {I : Type v}
    [PartialOrder I] (s : AffineStratification X I) {x : X} {i : I}
    (hx : x ∈ closure (s.strata i)) : ∃ j ≤ i, x ∈ s.strata j := by
  have hxLower := s.isLocallyFiniteStratification.isStratification.closure_subset i hx
  simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hxLower

private lemma strata_disjoint_closure_of_sameLevel {X : Scheme.{u}} {I : Type v}
    [PartialOrder I] [Finite I] {n : ℕ}
    (s : AffineStratification X I)
    (hn : Order.krullDim I = n) {i j : I}
    (hij : stratumLevel n i = stratumLevel n j) (hne : i ≠ j) :
    Disjoint (s.strata i) (closure (s.strata j)) := by
  apply Set.disjoint_left.mpr
  rintro x hxi hxj
  obtain ⟨k, hkj, hxk⟩ := exists_le_mem_strata_of_mem_closure s hxj
  obtain rfl := eq_of_mem_strata s hxk hxi
  exact (stratumLevel_strictMono hn (lt_of_le_of_ne hkj hne)).ne hij

private lemma levelStrata_isLocallyClosed {X : Scheme.{u}} {I : Type v}
    [PartialOrder I] [Finite I] {n : ℕ}
    (s : AffineStratification X I)
    (hn : Order.krullDim I = n) (k : Fin (n + 1)) :
    IsLocallyClosed (levelStrata n s k) := by
  classical
  let F : Set I := {i | stratumLevel n i = k}
  have hF : F.Finite := Set.toFinite F
  let Ui (i : I) : Set X :=
    coborder (s.strata i) ∩ (⋃ j ∈ F \ {i}, closure (s.strata j))ᶜ
  let U : Set X := ⋃ i ∈ F, Ui i
  let C : Set X := ⋃ i ∈ F, closure (s.strata i)
  have hUiopen (i : I) : IsOpen (Ui i) :=
    (s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed
      i).isOpen_coborder.inter
      ((hF.subset Set.sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure).isOpen_compl
  have hU : IsOpen U := isOpen_biUnion fun i _ => hUiopen i
  have hC : IsClosed C := hF.isClosed_biUnion fun _ _ => isClosed_closure
  have heq : levelStrata n s k = U ∩ C := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      refine ⟨?_, ?_⟩
      · simp only [U, Set.mem_iUnion₂]
        refine ⟨i.1, i.2, ?_⟩
        dsimp [Ui]
        change x ∈ coborder (s.strata i.1) ∧
          x ∉ ⋃ j ∈ F \ {i.1}, closure (s.strata j)
        constructor
        · change x ∉ closure (s.strata i.1) \ s.strata i.1
          exact fun h => h.2 hxi
        · intro hxj
          simp only [Set.mem_iUnion₂] at hxj
          obtain ⟨j, hji, hcx⟩ := hxj
          simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hji
          have hne : i.1 ≠ j := Ne.symm hji.2
          have hdis := strata_disjoint_closure_of_sameLevel s hn
            (i.2.trans hji.1.symm) hne
          exact hdis.le_bot ⟨hxi, hcx⟩
      · simp only [C, Set.mem_iUnion₂]
        exact ⟨i.1, i.2, subset_closure hxi⟩
    · rintro ⟨hxU, hxC⟩
      simp only [U, Set.mem_iUnion₂] at hxU
      obtain ⟨i, hi, hUi⟩ := hxU
      dsimp [Ui] at hUi
      simp only [C, Set.mem_iUnion₂] at hxC
      obtain ⟨j, hj, hxj⟩ := hxC
      by_cases hij : i = j
      · subst j
        apply Set.mem_iUnion.mpr
        refine ⟨⟨i, hi⟩, ?_⟩
        have hmem : x ∈ coborder (s.strata i) ∩ closure (s.strata i) :=
          ⟨hUi.1, hxj⟩
        rwa [coborder_inter_closure] at hmem
      · apply False.elim
        apply hUi.2
        have hji : j ≠ i := fun e => hij e.symm
        exact Set.mem_iUnion₂.mpr ⟨j, ⟨hj, hji⟩, hxj⟩
  exact ⟨U, C, hU, hC, heq⟩

private lemma levelStrata_isLocallyFiniteStratification {X : Scheme.{u}} {I : Type v}
    [PartialOrder I] [Finite I] {n : ℕ}
    (s : AffineStratification X I)
    (hn : Order.krullDim I = n) :
    IsLocallyFiniteStratification (levelStrata n s) := by
  classical
  refine ⟨⟨⟨fun k => levelStrata_isLocallyClosed s hn k, ?_, ?_⟩, ?_⟩,
    locallyFinite_of_finite _⟩
  · intro k l hkl
    apply Set.disjoint_left.mpr
    rintro x hx hx'
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx'
    by_cases hij : i.1 = j.1
    · have hlevels : k = l := by
        calc
          k = stratumLevel n i.1 := i.2.symm
          _ = stratumLevel n j.1 := congrArg (stratumLevel n) hij
          _ = l := j.2
      exact hkl hlevels
    · exact hij (eq_of_mem_strata s hxi hxj)
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, hxi⟩ := exists_mem_strata s x
    refine Set.mem_iUnion.mpr ⟨stratumLevel n i, ?_⟩
    exact Set.mem_iUnion.mpr ⟨⟨i, rfl⟩, hxi⟩
  · intro k
    change closure (⋃ i : {i : I // stratumLevel n i = k}, s.strata i.1) ⊆ _
    rw [Set.iUnion_subtype]
    change closure (⋃ i ∈ {i : I | stratumLevel n i = k}, s.strata i) ⊆ _
    rw [(Set.toFinite {i : I | stratumLevel n i = k}).closure_biUnion]
    apply Set.iUnion₂_subset
    intro i hi x hx
    obtain ⟨j, hji, hxj⟩ := exists_le_mem_strata_of_mem_closure s hx
    refine Set.mem_iUnion₂.mpr ⟨stratumLevel n j, ?_, ?_⟩
    · change stratumLevel n i = k at hi
      exact (stratumLevel_mono hn hji).trans (le_of_eq hi)
    · exact Set.mem_iUnion.mpr ⟨⟨j, rfl⟩, hxj⟩

/-- A closed immersion into a reduced scheme with open image is an open immersion. -/
private lemma isOpenImmersion_of_isClosedImmersion_isOpenRange
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsClosedImmersion f]
    (hopen : IsOpen (Set.range f)) [IsReduced Z] : IsOpenImmersion f := by
  let U : Z.Opens := ⟨Set.range f, hopen⟩
  let g : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι f (by
    rintro x ⟨y, rfl⟩
    exact ⟨⟨f y, ⟨y, rfl⟩⟩, rfl⟩)
  have hfac : g ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  have hgclosed : IsClosedImmersion g := by
    have hcomp : IsClosedImmersion (g ≫ U.ι) := by rw [hfac]; infer_instance
    let := hcomp
    exact IsClosedImmersion.of_comp g U.ι
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : U.ι y ∈ Set.range f := y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply U.ι.isEmbedding.injective
    simpa only [← Scheme.Hom.comp_apply, hfac] using hx
  let : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  let : IsClosedImmersion g := hgclosed
  let : Surjective g := ⟨hgsurj⟩
  have : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  have : IsOpenImmersion g := inferInstance
  rw [← hfac]
  infer_instance

private lemma closure_stratum_inter_level_subset {X : Scheme.{u}} {I : Type v}
    [PartialOrder I] [Finite I] {n : ℕ}
    (s : AffineStratification X I)
    (hn : Order.krullDim I = n) {k : Fin (n + 1)} {i : I}
    (hi : stratumLevel n i = k) :
    closure (s.strata i) ∩ levelStrata n s k ⊆ s.strata i := by
  rintro x ⟨hxcl, hxk⟩
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxk
  obtain ⟨m, hmi, hxm⟩ := exists_le_mem_strata_of_mem_closure s hxcl
  have hji : j.1 ≤ i := eq_of_mem_strata s hxm hxj ▸ hmi
  have hji' : j.1 = i := by
    by_contra hne
    exact (stratumLevel_strictMono hn (lt_of_le_of_ne hji hne)).ne (j.2.trans hi.symm)
  rwa [hji'] at hxj

private lemma levelStratum_isAffine {X : Scheme.{u}} {I : Type v}
    [PartialOrder I] [Finite I] {n : ℕ}
    (s : AffineStratification X I)
    (hn : Order.krullDim I = n) (k : Fin (n + 1)) :
    IsAffine
      (reducedInducedScheme (levelStrata n s k)
        (levelStrata_isLocallyClosed s hn k)) ∧
    IsAffineHom
      (reducedInducedInclusion (levelStrata n s k)
        (levelStrata_isLocallyClosed s hn k)) := by
  classical
  let T : Set X := levelStrata n s k
  let hT : IsLocallyClosed T := levelStrata_isLocallyClosed s hn k
  let Y := reducedInducedScheme T hT
  let f := reducedInducedInclusion T hT
  have hfrange : Set.range f = T := range_reducedInducedInclusion T hT
  let F := {i : I // stratumLevel n i = k}
  let : Finite F := Set.toFinite {i : I | stratumLevel n i = k} |>.to_subtype
  let Yi (i : F) := reducedInducedScheme (s.strata i.1)
    (s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i.1)
  let fi (i : F) := reducedInducedInclusion (s.strata i.1)
    (s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i.1)
  have hfirange (i : F) : Set.range (fi i) = s.strata i.1 :=
    range_reducedInducedInclusion _ _
  have hsubset (i : F) : Set.range (fi i) ⊆ T := by
    rw [hfirange i]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨i.1, i.2⟩, hx⟩
  let hYiRed (i : F) : IsReduced (Yi i) :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
      (reducedInducedClosed (s.strata i.1)
        (s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i.1))
  have hex (i : F) : ∃ g : Yi i ⟶ Y, g ≫ f = fi i :=
    exists_lift_reducedInduced T hT (fi i) (hsubset i)
  choose g hg using hex
  let hYRed : IsReduced Y :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
      (reducedInducedClosed T hT)
  let : IsPreimmersion f := inferInstance
  have hgf (i : F) (z : Yi i) : f (g i z) = fi i z := by
    simpa only [← Scheme.Hom.comp_apply] using congrArg (fun q => q z) (hg i)
  have hfT (y : Y) : f y ∈ T := by
    exact hfrange.le ⟨y, rfl⟩
  have hgPre (i : F) : IsPreimmersion (g i) := by
    have hcomp : IsPreimmersion (g i ≫ f) := by rw [hg i]; infer_instance
    exact IsPreimmersion.of_comp (g i) f
  have hgrange (i : F) : Set.range (g i) = f ⁻¹' s.strata i.1 := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change f (g i z) ∈ s.strata i.1
      have hmem : fi i z ∈ Set.range (fi i) := ⟨z, rfl⟩
      rw [hgf]
      simpa [hfirange i] using hmem
    · intro hy
      change f y ∈ s.strata i.1 at hy
      have hmem : f y ∈ Set.range (fi i) := by simpa [hfirange i] using hy
      obtain ⟨z, hz⟩ := hmem
      refine ⟨z, ?_⟩
      apply f.isEmbedding.injective
      calc
        f (g i z) = fi i z := hgf i z
        _ = f y := hz
  have hgrange_closed (i : F) : IsClosed (Set.range (g i)) := by
    rw [hgrange i]
    have hpre : f ⁻¹' s.strata i.1 = f ⁻¹' closure (s.strata i.1) := by
      ext y
      constructor
      · exact fun hy => subset_closure hy
      · intro hy
        exact closure_stratum_inter_level_subset s hn i.2 ⟨hy, hfT y⟩
    rw [hpre]
    exact isClosed_closure.preimage f.continuous
  have hcover : (⋃ i : F, Set.range (g i)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨i, hfi⟩ := Set.mem_iUnion.mp (hfT y)
    exact Set.mem_iUnion.mpr ⟨i, by rwa [hgrange i]⟩
  have hdis (i j : F) (hij : i ≠ j) :
      Disjoint (Set.range (g i)) (Set.range (g j)) := by
    apply Set.disjoint_left.mpr
    intro y hy hy'
    rw [hgrange i] at hy
    rw [hgrange j] at hy'
    exact hij (Subtype.ext (eq_of_mem_strata s hy hy'))
  have hopen (i : F) : IsOpen (Set.range (g i)) := by
    have hotherClosed : IsClosed (⋃ j ∈ {j : F | j ≠ i}, Set.range (g j)) :=
      (Set.toFinite {j : F | j ≠ i}).isClosed_biUnion fun j _ => hgrange_closed j
    have hcompl : (Set.range (g i))ᶜ =
        ⋃ j ∈ {j : F | j ≠ i}, Set.range (g j) := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · intro hy
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (show y ∈ ⋃ j : F, Set.range (g j) from
          by simp [hcover])
        have hji : j ≠ i := by
          intro h
          subst j
          exact hy hj
        exact ⟨j, hji, hj⟩
      · rintro ⟨j, hji, hj⟩ hy
        exact (hdis i j hji.symm).le_bot ⟨hy, hj⟩
    have hclosed : IsClosed ((Set.range (g i))ᶜ) := by
      rw [hcompl]
      exact hotherClosed
    simpa only [compl_compl] using hclosed.isOpen_compl
  have hgOpen (i : F) : IsOpenImmersion (g i) := by
    let : IsPreimmersion (g i) := hgPre i
    let : IsClosedImmersion (g i) := IsClosedImmersion.of_isPreimmersion _ (hgrange_closed i)
    exact isOpenImmersion_of_isClosedImmersion_isOpenRange (g i) (hopen i)
  let U (i : F) : Y.Opens := Scheme.Hom.opensRange (g i)
  have hUaff (i : F) : IsAffineOpen (U i) := by
    let : IsAffine (Yi i) := s.isAffine i.1
    simpa [U] using isAffineOpen_opensRange (g i)
  have hUdis : Pairwise (fun i j : F => Disjoint (U i) (U j)) := by
    intro i j hij
    apply (Opens.coe_disjoint (s := U i) (t := U j)).1
    simpa [U] using hdis i j hij
  have hUtop : (⨆ i : F, U i) = ⊤ := by
    apply SetLike.coe_injective
    rw [Opens.coe_iSup]
    ext y
    simp [U, Scheme.Hom.opensRange, hcover]
  have htopAffine : IsAffineOpen (⊤ : Y.Opens) := by
    rw [← hUtop]
    exact IsAffineOpen.iSup_of_disjoint hUaff hUdis
  let : IsAffine (⊤ : Y.Opens) := htopAffine
  have hYaffine : IsAffine Y := IsAffine.of_isIso Y.topIso.inv
  have hfAffineHom : IsAffineHom f := by
    constructor
    intro W hW
    let V (i : F) : Y.Opens := g i ''ᵁ ((fi i) ⁻¹ᵁ W)
    have hVaff (i : F) : IsAffineOpen (V i) := by
      let : IsAffineHom (fi i) := s.isAffineHom i.1
      have hpre : IsAffineOpen ((fi i) ⁻¹ᵁ W) := hW.preimage (fi i)
      let : IsOpenImmersion (g i) := hgOpen i
      exact hpre.image_of_isOpenImmersion (g i)
    have hVdis : Pairwise (fun i j : F => Disjoint (V i) (V j)) := by
      intro i j hij
      apply (Opens.coe_disjoint (s := V i) (t := V j)).1
      apply Set.disjoint_left.mpr
      intro y hy hy'
      change y ∈ (g i) '' ((fi i) ⁻¹ᵁ W : Set (Yi i)) at hy
      change y ∈ (g j) '' ((fi j) ⁻¹ᵁ W : Set (Yi j)) at hy'
      obtain ⟨zi, _, hzi⟩ := hy
      obtain ⟨zj, _, hzj⟩ := hy'
      have hyi : y ∈ Set.range (g i) := ⟨zi, hzi⟩
      have hyj : y ∈ Set.range (g j) := ⟨zj, hzj⟩
      exact (hdis i j hij).le_bot ⟨hyi, hyj⟩
    have hVeq : (⨆ i : F, V i) = f ⁻¹ᵁ W := by
      ext y
      rw [Opens.coe_iSup, Set.mem_iUnion]
      change (∃ i : F, y ∈ (g i) '' ((fi i) ⁻¹ᵁ W : Set (Yi i))) ↔ f y ∈ W
      constructor
      · rintro ⟨i, z, hzmem, hzy⟩
        have hzW : fi i z ∈ W := hzmem
        simpa only [← hzy, hgf] using hzW
      · intro hy
        have hycover : y ∈ ⋃ i : F, Set.range (g i) := by
          rw [hcover]
          simp
        obtain ⟨i, ⟨z, hzy⟩⟩ := Set.mem_iUnion.mp hycover
        refine ⟨i, z, ?_, hzy⟩
        change fi i z ∈ W
        simpa only [← hzy, hgf] using hy
    rw [← hVeq]
    exact IsAffineOpen.iSup_of_disjoint hVaff hVdis
  exact ⟨hYaffine, hfAffineHom⟩

/-- A finite affine stratification can be reindexed by the interval from zero
to the length of its indexing poset. -/
@[stacks 0F2T]
theorem exists_affineStratification_fin {X : Scheme.{u}}
    {I : Type v} [PartialOrder I] [Finite I]
    (s : AffineStratification X I) (n : ℕ)
    (hn : (Order.krullDim I = n) ∨ (IsEmpty I ∧ n = 0)) :
    Nonempty (AffineStratification X (Fin (n + 1))) := by
  classical
  rcases hn with hn | ⟨hI, rfl⟩
  · exact ⟨{
      strata := levelStrata n s
      isLocallyFiniteStratification := levelStrata_isLocallyFiniteStratification s hn
      isAffine := fun k => (levelStratum_isAffine s hn k).1
      isAffineHom := fun k => (levelStratum_isAffine s hn k).2 }⟩
  · have : IsEmpty X := ⟨fun x => by
      obtain ⟨i, -⟩ := exists_mem_strata s x
      exact hI.false i⟩
    let tStrata : Fin 1 → Set X := fun _ => ∅
    have hlf : IsLocallyFiniteStratification tStrata := by
      refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, locallyFinite_of_finite _⟩
      · intro i
        exact ⟨∅, Set.univ, isOpen_empty, isClosed_univ, by simp [tStrata]⟩
      · intro i j hij
        simp [tStrata]
      · rw [Set.eq_univ_iff_forall]
        intro x
        exact isEmptyElim x
      · intro i
        simp [tStrata]
    let t : AffineStratification X (Fin 1) := {
      strata := tStrata
      isLocallyFiniteStratification := hlf
      isAffine := by
        intro i
        let hLC : IsLocallyClosed (tStrata i) := hlf.isStratification.isPartition.locallyClosed i
        let : IsEmpty (reducedInducedScheme
            (tStrata i) hLC) :=
          ⟨fun y => isEmptyElim (reducedInducedInclusion
            (tStrata i) hLC y)⟩
        infer_instance
      isAffineHom := by
        intro i
        let hLC : IsLocallyClosed (tStrata i) := hlf.isStratification.isPartition.locallyClosed i
        let : IsEmpty (reducedInducedScheme
            (tStrata i) hLC) :=
          ⟨fun y => isEmptyElim (reducedInducedInclusion
            (tStrata i) hLC y)⟩
        let : IsAffine (reducedInducedScheme
          (tStrata i) hLC) := inferInstance
        let : IsAffine X := inferInstance
        infer_instance }
    exact ⟨by simpa using t⟩

end AlgebraicGeometry

end
