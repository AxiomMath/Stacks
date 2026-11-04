module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.ReducedInduced

/-!
# Affine stratifications of an affine scheme and of a union

This file supplies the two constructions out of which a finite affine stratification of a
quasi-compact quasi-separated scheme is assembled: an affine scheme is a single stratum, and a
union `U ⊔ V` of an open subscheme `U` and an affine open `V` inherits an affine stratification
from affine stratifications of `U` and of `U ⊓ V`.

## Main results

* `AlgebraicGeometry.AffineStratification.ofIso`: transport of an affine stratification along
  an isomorphism of schemes.
* `AlgebraicGeometry.AffineStratification.ofIsAffine`: the one-stratum affine stratification of
  an affine scheme.
* `AlgebraicGeometry.AffineStratification.ofSup`: the affine stratification of `U ⊔ V` built
  from affine stratifications of `U` and of `U ⊓ V`, with `V` affine.

## Implementation notes

The strata of `U ⊔ V` are indexed by `WithBot (I × WithBot J)`: the bottom index carries the
part of `V` outside `U`, the index `(i, ⊥)` carries the part of the `i`-th stratum of `U`
outside `V`, and `(i, j)` carries the intersection of the `i`-th stratum of `U` with the `j`-th
stratum of `U ⊓ V`. Affineness of a stratum and of its inclusion is checked by exhibiting an
affine scheme mapping onto it by an affine immersion, using
`AlgebraicGeometry.isAffine_reducedInduced_of_range_eq`; affineness of the inclusion into
`U ⊔ V` is itself checked on the open cover by `U` and `V`.

## References

* [Stacks Project, Tag 0F2U](https://stacks.math.columbia.edu/tag/0F2U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u v

namespace AlgebraicGeometry

/-! ### Checking affineness of a morphism on an open cover of the target -/

/-- If a morphism `f` factors as an affine morphism into an open subscheme `U`, then the
inverse image under `f` of every affine open contained in `U` is affine. -/
theorem isAffineOpen_preimage_of_factorisation {X Y : Scheme.{u}} {f : Y ⟶ X} {U : X.Opens}
    (g : Y ⟶ U.toScheme) (hg : g ≫ U.ι = f) [IsAffineHom g] {W : X.Opens}
    (hW : IsAffineOpen W) (hWU : W ≤ U) : IsAffineOpen (f ⁻¹ᵁ W) := by
  have hpre : f ⁻¹ᵁ W = g ⁻¹ᵁ (U.ι ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hg]
  rw [hpre]
  exact (hW.preimage_of_isOpenImmersion U.ι (by simpa using hWU)).preimage g

/-- A point of `U` lies in an affine open whose preimage is affine, when the morphism factors as
an affine morphism into `U`. -/
private theorem exists_isAffineOpen_preimage_of_factorisation {X Y : Scheme.{u}} {f : Y ⟶ X}
    {U : X.Opens} (g : Y ⟶ U.toScheme) (hg : g ≫ U.ι = f) [IsAffineHom g] {x : X} (hx : x ∈ U) :
    ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨W, hxW, hW, isAffineOpen_preimage_of_factorisation g hg hW hWU⟩

/-- A point of the target lies in `U` or in `V` when `U ⊔ V = ⊤`. -/
private theorem mem_or_mem_of_sup_eq_top {X : Scheme.{u}} {U V : X.Opens} (hcover : U ⊔ V = ⊤)
    (x : X) : x ∈ U ∨ x ∈ V := by
  have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
  simpa using hx

/-- A morphism is affine as soon as it factors as an affine morphism into each of two open
subschemes covering the target. -/
theorem isAffineHom_of_factorisations {X Y : Scheme.{u}} (f : Y ⟶ X) (U V : X.Opens)
    (gU : Y ⟶ U.toScheme) (gV : Y ⟶ V.toScheme) (hU : gU ≫ U.ι = f) (hV : gV ≫ V.ι = f)
    [IsAffineHom gU] [IsAffineHom gV] (hcover : U ⊔ V = ⊤) : IsAffineHom f := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  rcases mem_or_mem_of_sup_eq_top hcover x with hx | hx
  · exact exists_isAffineOpen_preimage_of_factorisation gU hU hx
  · exact exists_isAffineOpen_preimage_of_factorisation gV hV hx

/-- A morphism is affine as soon as it factors as an affine morphism into an open subscheme
`U` and misses a second open subscheme `V` with `U ⊔ V = ⊤`. -/
theorem isAffineHom_of_factorisation_of_preimage_eq_bot {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U V : X.Opens) (gU : Y ⟶ U.toScheme) (hU : gU ≫ U.ι = f) [IsAffineHom gU]
    (hcover : U ⊔ V = ⊤) (hempty : f ⁻¹ᵁ V = ⊥) : IsAffineHom f := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  rcases mem_or_mem_of_sup_eq_top hcover x with hx | hx
  · exact exists_isAffineOpen_preimage_of_factorisation gU hU hx
  · obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨W, hxW, hW, ?_⟩
    have hbot : f ⁻¹ᵁ W = ⊥ :=
      le_bot_iff.mp (hempty.le.trans' (Scheme.Hom.preimage_mono f hWV))
    rw [hbot]
    exact isAffineOpen_bot _

/-! ### Transport along an isomorphism -/

/-- An affine stratification transports along an isomorphism of schemes. -/
noncomputable def AffineStratification.ofIso {X Y : Scheme.{u}} {I : Type v} [PartialOrder I]
    (e : Y ≅ X) (s : AffineStratification X I) : AffineStratification Y I := by
  let φ : Y ≃ₜ X := Scheme.homeoOfIso e
  let strata : I → Set Y := fun i => e.hom.base ⁻¹' s.strata i
  have hlf : IsLocallyFiniteStratification strata := by
    refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_, ?_⟩, fun j => ?_⟩, fun y => ?_⟩
    · exact (s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed
        i).preimage e.hom.continuous
    · exact Set.disjoint_left.mpr fun y hyi hyj =>
        (s.isLocallyFiniteStratification.isStratification.isPartition.disjoint
          i j hij).le_bot ⟨hyi, hyj⟩
    · refine Set.eq_univ_of_forall fun y => ?_
      have hx : e.hom y ∈ ⋃ i, s.strata i := by
        rw [s.isLocallyFiniteStratification.isStratification.isPartition.cover]
        exact Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · have hcl : closure (strata j) = e.hom.base ⁻¹' closure (s.strata j) :=
        (φ.preimage_closure (s.strata j)).symm
      rw [hcl]
      simpa only [strata, Set.preimage_iUnion] using Set.preimage_mono
        (s.isLocallyFiniteStratification.isStratification.closure_subset j)
    · obtain ⟨t, ht, hfinite⟩ := s.isLocallyFiniteStratification.locallyFinite (e.hom y)
      refine ⟨e.hom.base ⁻¹' t, e.hom.continuous.tendsto y ht, ?_⟩
      have heq : {i | (strata i ∩ e.hom.base ⁻¹' t).Nonempty} =
          {i | (s.strata i ∩ t).Nonempty} := by
        ext i
        constructor
        · rintro ⟨z, hzS, hzt⟩
          exact ⟨e.hom z, hzS, hzt⟩
        · rintro ⟨x, hxS, hxt⟩
          obtain ⟨z, rfl⟩ := φ.surjective x
          exact ⟨z, hxS, hxt⟩
      rw [heq]
      exact hfinite
  have hAff (i : I) : IsAffine (reducedInducedScheme (strata i)
      (hlf.isStratification.isPartition.locallyClosed i)) ∧
      IsAffineHom (reducedInducedInclusion (strata i)
        (hlf.isStratification.isPartition.locallyClosed i)) := by
    let hOldLC := s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i
    let f := reducedInducedInclusion (s.strata i) hOldLC
    have : IsAffine (reducedInducedScheme (s.strata i) hOldLC) := s.isAffine i
    have : IsAffineHom f := s.isAffineHom i
    have : IsImmersion (f ≫ e.inv) := inferInstance
    have : IsAffineHom (f ≫ e.inv) := inferInstance
    have hrange : Set.range (f ≫ e.inv) = strata i := by
      change Set.range (e.inv.base ∘ f.base) = e.hom.base ⁻¹' s.strata i
      rw [Set.range_comp, range_reducedInducedInclusion]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨e.hom y, hy, by simp⟩
    exact isAffine_reducedInduced_of_range_eq (strata i) _ (f ≫ e.inv) hrange
  exact { strata := strata
          isLocallyFiniteStratification := hlf
          isAffine := fun i => (hAff i).1
          isAffineHom := fun i => (hAff i).2 }

/-! ### The affine stratification of an affine scheme -/

/-- An affine scheme is a single stratum: the affine stratification of an affine scheme indexed
by any nonempty one-element poset. -/
noncomputable def AffineStratification.ofIsAffine {I : Type v} [PartialOrder I] [Subsingleton I]
    [Nonempty I] (X : Scheme.{u}) [IsAffine X] : AffineStratification X I := by
  have : Finite I := Finite.of_subsingleton
  let strata : I → Set X := fun _ => Set.univ
  have hlf : IsLocallyFiniteStratification strata := by
    refine ⟨⟨⟨fun i => isOpen_univ.isLocallyClosed, fun i j hij => (hij
      (Subsingleton.elim _ _)).elim, ?_⟩, fun i x _ => ?_⟩, locallyFinite_of_finite _⟩
    · exact Set.eq_univ_of_forall fun x =>
        Set.mem_iUnion.mpr ⟨Classical.arbitrary I, Set.mem_univ x⟩
    · exact Set.mem_iUnion₂.mpr ⟨i, Set.mem_ofPred_eq.mpr le_rfl, Set.mem_univ x⟩
  have hAff (i : I) : IsAffine (reducedInducedScheme (strata i)
      (hlf.isStratification.isPartition.locallyClosed i)) ∧
      IsAffineHom (reducedInducedInclusion (strata i)
        (hlf.isStratification.isPartition.locallyClosed i)) := by
    simpa [strata] using
      isAffine_reducedInduced_of_isClosed (⟨Set.univ, isClosed_univ⟩ : Closeds X)
  exact { strata := strata
          isLocallyFiniteStratification := hlf
          isAffine := fun i => (hAff i).1
          isAffineHom := fun i => (hAff i).2 }

/-! ### The union of an open subscheme and an affine open -/

/-- If the open subscheme `U` and the open subscheme `U ⊓ V` carry finite affine stratifications
and `V` is an affine open, then `U ⊔ V` carries an affine stratification indexed by
`WithBot (I × WithBot J)`. -/
noncomputable def AffineStratification.ofSup {X : Scheme.{u}} (U V : X.Opens)
    (hV : IsAffineOpen V) {I J : Type v} [PartialOrder I] [PartialOrder J] [Finite I] [Finite J]
    (sU : AffineStratification U.toScheme I)
    (sUV : AffineStratification (U ⊓ V).toScheme J) :
    AffineStratification (U ⊔ V).toScheme (WithBot (I × WithBot J)) := by
  classical
  have : Finite (WithBot J) := inferInstanceAs (Finite (Option J))
  have : Finite (WithBot (I × WithBot J)) := inferInstanceAs (Finite (Option (I × WithBot J)))
  let W : X.Opens := U ⊔ V
  let U' : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  let V' : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  let O' : W.toScheme.Opens := W.ι ⁻¹ᵁ (U ⊓ V)
  have hVaff : IsAffineOpen V' := hV.preimage_of_isOpenImmersion W.ι (by simp [W])
  let eU : U'.toScheme ≅ U.toScheme := Scheme.Opens.isoOfLE (le_sup_left : U ≤ W)
  let eO : O'.toScheme ≅ (U ⊓ V).toScheme :=
    Scheme.Opens.isoOfLE (inf_le_left.trans (le_sup_left : U ≤ W))
  let sU' := AffineStratification.ofIso eU sU
  let sO' := AffineStratification.ofIso eO sUV
  have hUcover : U' ⊔ V' = ⊤ := by
    ext x
    refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
    change x.1 ∈ U ∨ x.1 ∈ V
    simpa [W] using x.property
  have hOsubU : O' ≤ U' := fun x hx => hx.1
  have hOsubV : O' ≤ V' := fun x hx => hx.2
  let jOU : O'.toScheme ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι O'.ι
    (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact hOsubU)
  let jOV : O'.toScheme ⟶ V'.toScheme := IsOpenImmersion.lift V'.ι O'.ι
    (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact hOsubV)
  have hjOU : jOU ≫ U'.ι = O'.ι := IsOpenImmersion.lift_fac _ _ _
  have hjOV : jOV ≫ V'.ι = O'.ι := IsOpenImmersion.lift_fac _ _ _
  let Ui : I → Set W.toScheme := fun i => U'.ι.base '' sU'.strata i
  let Wj : J → Set W.toScheme := fun j => O'.ι.base '' sO'.strata j
  have hUemb : Topology.IsOpenEmbedding U'.ι.base := U'.ι.isOpenEmbedding
  have hOemb : Topology.IsOpenEmbedding O'.ι.base := O'.ι.isOpenEmbedding
  have hmemU (y : U'.toScheme) : U'.ι y ∈ (U' : Set W.toScheme) := y.property
  let strata : WithBot (I × WithBot J) → Set W.toScheme
    | ⊥ => (U' : Set W.toScheme)ᶜ
    | .some (i, ⊥) => Ui i \ (V' : Set W.toScheme)
    | .some (i, .some j) => Ui i ∩ Wj j
  have hUiLC (i : I) : IsLocallyClosed (Ui i) :=
    (sU'.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i).image
      hUemb.isInducing hUemb.isOpen_range.isLocallyClosed
  have hWjLC (j : J) : IsLocallyClosed (Wj j) :=
    (sO'.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed j).image
      hOemb.isInducing hOemb.isOpen_range.isLocallyClosed
  have hUiCover : (⋃ (i : I), Ui i) = (U' : Set W.toScheme) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hmemU y
    · intro hx
      obtain ⟨y, rfl⟩ : x ∈ Set.range U'.ι.base := by rw [Scheme.Opens.range_ι]; exact hx
      have hy : y ∈ Set.iUnion sU'.strata := by
        rw [sU'.isLocallyFiniteStratification.isStratification.isPartition.cover]
        exact Set.mem_univ y
      obtain ⟨i, hy⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨i, ⟨y, hy, rfl⟩⟩
  have hWjCover : (⋃ (j : J), Wj j) = (O' : Set W.toScheme) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨j, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact y.property
    · intro hx
      obtain ⟨y, rfl⟩ : x ∈ Set.range O'.ι.base := by rw [Scheme.Opens.range_ι]; exact hx
      have hy : y ∈ Set.iUnion sO'.strata := by
        rw [sO'.isLocallyFiniteStratification.isStratification.isPartition.cover]
        exact Set.mem_univ y
      obtain ⟨j, hy⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨j, ⟨y, hy, rfl⟩⟩
  have hUiDisjoint {i i' : I} (hne : i ≠ i') : Disjoint (Ui i) (Ui i') := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    obtain rfl : z = y := hUemb.injective heq
    exact (sU'.isLocallyFiniteStratification.isStratification.isPartition.disjoint
      i i' hne).le_bot ⟨hy, hz⟩
  have hWjDisjoint {j j' : J} (hne : j ≠ j') : Disjoint (Wj j) (Wj j') := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    obtain rfl : z = y := hOemb.injective heq
    exact (sO'.isLocallyFiniteStratification.isStratification.isPartition.disjoint
      j j' hne).le_bot ⟨hy, hz⟩
  have hWjV (j : J) : Wj j ⊆ (V' : Set W.toScheme) := by
    rintro x ⟨y, hy, rfl⟩
    exact hOsubV y.property
  have hpreUi (i : I) : U'.ι.base ⁻¹' closure (Ui i) = closure (sU'.strata i) := by
    rw [hUemb.isOpenMap.preimage_closure_eq_closure_preimage U'.ι.continuous]
    simp [Ui, Set.preimage_image_eq _ hUemb.injective]
  have hpreWj (j : J) : O'.ι.base ⁻¹' closure (Wj j) = closure (sO'.strata j) := by
    rw [hOemb.isOpenMap.preimage_closure_eq_closure_preimage O'.ι.continuous]
    simp [Wj, Set.preimage_image_eq _ hOemb.injective]
  have hUiLower (i : I) {x : W.toScheme} (hxU : x ∈ (U' : Set W.toScheme))
      (hxc : x ∈ closure (Ui i)) : ∃ k, k ≤ i ∧ x ∈ Ui k := by
    obtain ⟨y, rfl⟩ : x ∈ Set.range U'.ι.base := by rw [Scheme.Opens.range_ι]; exact hxU
    have hyc : y ∈ closure (sU'.strata i) := by rw [← hpreUi]; exact hxc
    have hlower := sU'.isLocallyFiniteStratification.isStratification.closure_subset i hyc
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hlower
    obtain ⟨k, hki, hyk⟩ := hlower
    exact ⟨k, hki, ⟨y, hyk, rfl⟩⟩
  have hWjLower (j : J) {x : W.toScheme} (hxO : x ∈ (O' : Set W.toScheme))
      (hxc : x ∈ closure (Wj j)) : ∃ l, l ≤ j ∧ x ∈ Wj l := by
    obtain ⟨y, rfl⟩ : x ∈ Set.range O'.ι.base := by rw [Scheme.Opens.range_ι]; exact hxO
    have hyc : y ∈ closure (sO'.strata j) := by rw [← hpreWj]; exact hxc
    have hlower := sO'.isLocallyFiniteStratification.isStratification.closure_subset j hyc
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hlower
    obtain ⟨l, hlj, hyk⟩ := hlower
    exact ⟨l, hlj, ⟨y, hyk, rfl⟩⟩
  have hlf : IsLocallyFiniteStratification strata := by
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, locallyFinite_of_finite strata⟩
    · intro a
      cases a with
      | bot => exact U'.2.isClosed_compl.isLocallyClosed
      | coe p =>
        obtain ⟨i, j⟩ := p
        cases j with
        | bot =>
          change IsLocallyClosed (Ui i ∩ (V' : Set W.toScheme)ᶜ)
          exact (hUiLC i).inter V'.2.isClosed_compl.isLocallyClosed
        | coe j => exact (hUiLC i).inter (hWjLC j)
    · intro a b hab
      apply Set.disjoint_left.mpr
      intro x hxa hxb
      cases a with
      | bot =>
        cases b with
        | bot => exact (hab rfl).elim
        | coe p =>
          obtain ⟨i, j⟩ := p
          cases j with
          | bot =>
            obtain ⟨y, hy, rfl⟩ := hxb.1
            exact hxa (hmemU y)
          | coe j =>
            obtain ⟨y, hy, rfl⟩ := hxb.1
            exact hxa (hmemU y)
      | coe p =>
        obtain ⟨i, j⟩ := p
        cases j with
        | bot =>
          cases b with
          | bot =>
            obtain ⟨y, hy, rfl⟩ := hxa.1
            exact hxb (hmemU y)
          | coe q =>
            obtain ⟨i', j'⟩ := q
            cases j' with
            | bot =>
              by_cases hii : i = i'
              · exact (hab (by rw [hii])).elim
              · exact (hUiDisjoint hii).le_bot ⟨hxa.1, hxb.1⟩
            | coe j' => exact hxa.2 (hWjV j' hxb.2)
        | coe j =>
          cases b with
          | bot =>
            obtain ⟨y, hy, rfl⟩ := hxa.1
            exact hxb (hmemU y)
          | coe q =>
            obtain ⟨i', j'⟩ := q
            cases j' with
            | bot => exact hxb.2 (hWjV j hxa.2)
            | coe j' =>
              by_cases hii : i = i'
              · subst i'
                by_cases hjj : j = j'
                · exact (hab (by rw [hjj])).elim
                · exact (hWjDisjoint hjj).le_bot ⟨hxa.2, hxb.2⟩
              · exact (hUiDisjoint hii).le_bot ⟨hxa.1, hxb.1⟩
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hxU : x ∈ (U' : Set W.toScheme)
      · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hUiCover ▸ hxU)
        by_cases hxV : x ∈ (V' : Set W.toScheme)
        · have hxO : x ∈ (O' : Set W.toScheme) := ⟨hxU, hxV⟩
          obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hWjCover ▸ hxO)
          exact ⟨.some (i, .some j), ⟨hxi, hxj⟩⟩
        · exact ⟨.some (i, ⊥), hxi, hxV⟩
      · exact ⟨⊥, hxU⟩
    · intro a x hx
      cases a with
      | bot =>
        have hclosed : IsClosed (strata (⊥ : WithBot (I × WithBot J))) := U'.2.isClosed_compl
        rw [hclosed.closure_eq] at hx
        exact Set.mem_iUnion₂.mpr ⟨⊥, by simp, hx⟩
      | coe p =>
        obtain ⟨i, j⟩ := p
        cases j with
        | bot =>
          have hxUi : x ∈ closure (Ui i) := closure_mono (fun y hy => hy.1) hx
          have hxNotV : x ∉ (V' : Set W.toScheme) :=
            closure_minimal (fun y hy => hy.2) V'.2.isClosed_compl hx
          by_cases hxU : x ∈ (U' : Set W.toScheme)
          · obtain ⟨k, hki, hxk⟩ := hUiLower i hxU hxUi
            exact Set.mem_iUnion₂.mpr ⟨.some (k, ⊥),
              WithBot.coe_le_coe.mpr ⟨hki, le_rfl⟩, ⟨hxk, hxNotV⟩⟩
          · exact Set.mem_iUnion₂.mpr ⟨⊥, by simp, hxU⟩
        | coe j =>
          have hxUi : x ∈ closure (Ui i) := closure_mono (fun y hy => hy.1) hx
          have hxWj : x ∈ closure (Wj j) := closure_mono (fun y hy => hy.2) hx
          by_cases hxU : x ∈ (U' : Set W.toScheme)
          · obtain ⟨k, hki, hxk⟩ := hUiLower i hxU hxUi
            by_cases hxV : x ∈ (V' : Set W.toScheme)
            · have hxO : x ∈ (O' : Set W.toScheme) := ⟨hxU, hxV⟩
              obtain ⟨l, hlj, hxl⟩ := hWjLower j hxO hxWj
              exact Set.mem_iUnion₂.mpr ⟨.some (k, .some l),
                WithBot.coe_le_coe.mpr ⟨hki, WithBot.coe_le_coe.mpr hlj⟩, ⟨hxk, hxl⟩⟩
            · exact Set.mem_iUnion₂.mpr ⟨.some (k, ⊥),
                WithBot.coe_le_coe.mpr ⟨hki, bot_le⟩, ⟨hxk, hxV⟩⟩
          · exact Set.mem_iUnion₂.mpr ⟨⊥, by simp, hxU⟩
  have hIbot (i : I) :
      IsAffine (reducedInducedScheme (strata (.some (i, ⊥)))
        (hlf.isStratification.isPartition.locallyClosed (.some (i, ⊥)))) ∧
      IsAffineHom (reducedInducedInclusion (strata (.some (i, ⊥)))
        (hlf.isStratification.isPartition.locallyClosed (.some (i, ⊥)))) := by
    let hLC := sU'.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i
    let A := reducedInducedScheme (sU'.strata i) hLC
    let f := reducedInducedInclusion (sU'.strata i) hLC
    let m : A ⟶ W.toScheme := f ≫ U'.ι
    let C : Closeds A :=
      ⟨m.base ⁻¹' (V' : Set W.toScheme)ᶜ, V'.2.isClosed_compl.preimage m.continuous⟩
    let K := Scheme.IdealSheafData.vanishingIdeal C
    let g : K.subscheme ⟶ W.toScheme := K.subschemeι ≫ m
    have hfRange : Set.range f.base = sU'.strata i := range_reducedInducedInclusion _ _
    have hrange : Set.range g.base = strata (.some (i, ⊥)) := by
      change Set.range (m.base ∘ K.subschemeι.base) = _
      rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      change m.base '' (C : Set A) = Ui i \ (V' : Set W.toScheme)
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨f y, hfRange.le ⟨y, rfl⟩, rfl⟩, hy⟩
      · rintro ⟨⟨z, hz, rfl⟩, hxV⟩
        obtain ⟨y, hy⟩ : z ∈ Set.range f.base := hfRange.ge hz
        exact ⟨y, by change U'.ι.base (f.base y) ∉ _; rw [hy]; exact hxV,
          by change U'.ι.base (f.base y) = U'.ι.base z; rw [hy]⟩
    have hpre : g ⁻¹ᵁ V' = ⊥ := by
      ext z
      exact ⟨fun hz => absurd hz (hrange.le ⟨z, rfl⟩).2, fun hz => by simp at hz⟩
    have : IsAffine A := sU'.isAffine i
    have : IsAffineHom f := sU'.isAffineHom i
    have : IsAffine K.subscheme := isAffine_of_isAffineHom K.subschemeι
    have : IsImmersion g := by dsimp [g, m]; infer_instance
    have hfac : (K.subschemeι ≫ f) ≫ U'.ι = g := by simp [g, m]
    have : IsAffineHom g :=
      isAffineHom_of_factorisation_of_preimage_eq_bot g U' V'
        (K.subschemeι ≫ f) hfac hUcover hpre
    exact isAffine_reducedInduced_of_range_eq (strata (.some (i, ⊥)))
      (hlf.isStratification.isPartition.locallyClosed (.some (i, ⊥))) g hrange
  have hbotLC := hlf.isStratification.isPartition.locallyClosed (⊥ : WithBot (I × WithBot J))
  have hbot : IsAffine (reducedInducedScheme (strata ⊥) hbotLC) ∧
      IsAffineHom (reducedInducedInclusion (strata ⊥) hbotLC) := by
    let C : Closeds V'.toScheme :=
      ⟨V'.ι.base ⁻¹' (U' : Set W.toScheme)ᶜ, U'.2.isClosed_compl.preimage V'.ι.continuous⟩
    let K := Scheme.IdealSheafData.vanishingIdeal C
    let g : K.subscheme ⟶ W.toScheme := K.subschemeι ≫ V'.ι
    have hCimage : V'.ι.base '' (C : Set V'.toScheme) = (U' : Set W.toScheme)ᶜ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxcover : x ∈ (U' ⊔ V' : W.toScheme.Opens) := by
          rw [hUcover]; exact Set.mem_univ x
        have hxV : x ∈ (V' : Set W.toScheme) :=
          ((by simpa using hxcover : x ∈ (U' : Set W.toScheme) ∨
            x ∈ (V' : Set W.toScheme))).resolve_left hx
        obtain ⟨y, hy⟩ : x ∈ Set.range V'.ι.base := by rw [Scheme.Opens.range_ι]; exact hxV
        exact ⟨y, show V'.ι.base y ∈ (U' : Set W.toScheme)ᶜ by rw [hy]; exact hx, hy⟩
    have hrange : Set.range g.base = strata ⊥ := by
      change Set.range (V'.ι.base ∘ K.subschemeι.base) = _
      rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      exact hCimage
    have : IsAffine V'.toScheme := hVaff
    have : IsAffine K.subscheme := isAffine_of_isAffineHom K.subschemeι
    have : IsImmersion g := by dsimp [g]; infer_instance
    have hcover' : V' ⊔ U' = ⊤ := by rw [sup_comm, hUcover]
    have hempty : g ⁻¹ᵁ U' = ⊥ := by
      ext z
      exact ⟨fun hz => absurd hz (hrange.le ⟨z, rfl⟩), fun hz => by simp at hz⟩
    have : IsAffineHom g :=
      isAffineHom_of_factorisation_of_preimage_eq_bot g V' U' K.subschemeι rfl hcover' hempty
    exact isAffine_reducedInduced_of_range_eq (strata ⊥) hbotLC g hrange
  have hIcross (i : I) (j : J) :
      IsAffine (reducedInducedScheme (strata (.some (i, .some j)))
        (hlf.isStratification.isPartition.locallyClosed (.some (i, .some j)))) ∧
      IsAffineHom (reducedInducedInclusion (strata (.some (i, .some j)))
        (hlf.isStratification.isPartition.locallyClosed (.some (i, .some j)))) := by
    let hUiLC' := sU'.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i
    let hWjLC' := sO'.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed j
    let A := reducedInducedScheme (sU'.strata i) hUiLC'
    let R := reducedInducedScheme (sO'.strata j) hWjLC'
    let f := reducedInducedInclusion (sU'.strata i) hUiLC'
    let q := reducedInducedInclusion (sO'.strata j) hWjLC'
    let t : R ⟶ U'.toScheme := q ≫ jOU
    let r : R ⟶ V'.toScheme := q ≫ jOV
    let P := pullback f t
    let pA : P ⟶ A := pullback.fst f t
    let pR : P ⟶ R := pullback.snd f t
    let gU : P ⟶ U'.toScheme := pA ≫ f
    let gV : P ⟶ V'.toScheme := pR ≫ r
    let g : P ⟶ W.toScheme := gU ≫ U'.ι
    have hfRange : Set.range f.base = sU'.strata i := range_reducedInducedInclusion _ _
    have hqRange : Set.range q.base = sO'.strata j := range_reducedInducedInclusion _ _
    have htRange : Set.range t.base = jOU.base '' sO'.strata j := by
      change Set.range (jOU.base ∘ q.base) = _
      rw [Set.range_comp, hqRange]
    have hrange : Set.range g.base = strata (.some (i, .some j)) := by
      change Set.range (((pA ≫ f) ≫ U'.ι).base) = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      change U'.ι.base '' Set.range (pullback.fst f t ≫ f).base = _
      rw [Scheme.Pullback.range_fst_comp, hfRange, htRange]
      rw [Set.image_inter hUemb.injective]
      have hbase : (fun x => U'.ι (jOU x)) = O'.ι := by
        funext x
        change (jOU ≫ U'.ι) x = O'.ι x
        rw [hjOU]
      rw [Set.image_image, hbase]
    have hfacV : gV ≫ V'.ι = g := by
      calc
        gV ≫ V'.ι = (pR ≫ t) ≫ U'.ι := by
          dsimp [gV, r, t]
          simp only [Category.assoc, hjOV, ← hjOU]
        _ = (pA ≫ f) ≫ U'.ι :=
          congrArg (fun k : P ⟶ U'.toScheme => k ≫ U'.ι)
            (pullback.condition (f := f) (g := t)).symm
        _ = g := rfl
    have : IsAffine A := sU'.isAffine i
    have : IsAffine R := sO'.isAffine j
    have : IsAffine V'.toScheme := hVaff
    have : IsAffineHom f := sU'.isAffineHom i
    have : IsAffineHom q := sO'.isAffineHom j
    have : IsAffine P := by dsimp [P]; infer_instance
    have : IsAffineHom pA := by dsimp [pA]; infer_instance
    have : IsAffineHom pR := by dsimp [pR]; infer_instance
    have : IsAffineHom gU := by dsimp [gU]; infer_instance
    have : IsAffineHom r := by dsimp [r]; infer_instance
    have : IsAffineHom gV := by dsimp [gV, r]; infer_instance
    have : IsImmersion g := by dsimp [g, gU]; infer_instance
    have : IsAffineHom g := isAffineHom_of_factorisations g U' V' gU gV rfl hfacV hUcover
    exact isAffine_reducedInduced_of_range_eq (strata (.some (i, .some j)))
      (hlf.isStratification.isPartition.locallyClosed (.some (i, .some j))) g hrange
  exact { strata := strata
          isLocallyFiniteStratification := hlf
          isAffine := by
            intro a
            cases a with
            | bot => exact hbot.1
            | coe p =>
              obtain ⟨i, j⟩ := p
              cases j with
              | bot => exact (hIbot i).1
              | coe j => exact (hIcross i j).1
          isAffineHom := by
            intro a
            cases a with
            | bot => exact hbot.2
            | coe p =>
              obtain ⟨i, j⟩ := p
              cases j with
              | bot => exact (hIbot i).2
              | coe j => exact (hIcross i j).2 }

end AlgebraicGeometry

end
