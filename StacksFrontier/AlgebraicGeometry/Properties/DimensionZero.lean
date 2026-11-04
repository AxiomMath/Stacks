module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.Tactic.TFAE
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.Separated
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite

/-!
# Schemes of dimension zero

For a scheme of dimension zero the separation properties all collapse into one another: being
quasi-separated, being separated, having Hausdorff underlying space, and having every affine open
closed are four equivalent conditions. When they hold, the connected components of the scheme are
its points, every quasi-compact open subset is affine, and in particular a quasi-compact
zero-dimensional scheme is affine.

## Main results

* `AlgebraicGeometry.separation_tfae_of_topologicalKrullDim_eq_zero`: the four equivalent
  separation properties of a zero-dimensional scheme.
* `AlgebraicGeometry.connectedComponent_eq_singleton_of_topologicalKrullDim_eq_zero`: the
  connected components of a quasi-separated zero-dimensional scheme are points.
* `AlgebraicGeometry.isAffineOpen_of_isCompact_of_topologicalKrullDim_eq_zero`: every
  quasi-compact open of a quasi-separated zero-dimensional scheme is affine.
* `AlgebraicGeometry.isAffine_of_topologicalKrullDim_eq_zero`: a quasi-compact quasi-separated
  zero-dimensional scheme is affine.

## Implementation notes

The dimension of a scheme is the Krull dimension `topologicalKrullDim` of its underlying space,
quasi-compactness of an open subset is compactness of its carrier, and quasi-separatedness is
`QuasiSeparatedSpace` on the underlying space. The entries of the `List.TFAE` are the four items
of the source, in order.

## References

* [Stacks Project, Tag 0CKV](https://stacks.math.columbia.edu/tag/0CKV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A nonempty space of nonpositive Krull dimension has dimension exactly zero. -/
private lemma topologicalKrullDim_eq_zero_of_nonempty_of_le {Y : Type u}
    [TopologicalSpace Y] (hne : Nonempty Y) (hle : topologicalKrullDim Y ≤ 0) :
    topologicalKrullDim Y = 0 := by
  let : Nonempty (IrreducibleCloseds Y) :=
    ⟨⟨closure {Classical.choice hne}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm hle Order.krullDim_nonneg

/-- A quasi-compact open subset of a zero-dimensional affine scheme is closed, and is itself an
affine open. -/
private lemma isClosed_and_isAffineOpen_of_isCompact_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (hX : topologicalKrullDim X = 0) (W : X.Opens) (hW : IsCompact (W : Set X)) :
    IsClosed (W : Set X) ∧ IsAffineOpen W := by
  have hspecializes : ∀ x y : X, x ⤳ y → x = y := by
    have hmax : ∀ Z : IrreducibleCloseds X, IsMax Z :=
      Order.krullDim_nonpos_iff_forall_isMax.mp (by
        simpa [topologicalKrullDim] using hX.le)
    intro x y hxy
    have heq : (⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds X) = ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      (hmax _).eq_of_le hxy.closure_subset
    have hcl : closure ({y} : Set X) = closure {x} :=
      congrArg (fun Z : IrreducibleCloseds X ↦ (Z : Set X)) heq
    exact T0Space.t0 (by simpa [inseparable_iff_closure_eq] using hcl.symm)
  let e := X.isoSpec.schemeIsoToHomeo
  have himage_stable : StableUnderSpecialization (e '' (W : Set X)) := by
    intro x y hxy hx
    have heq : x = y := by
      simpa using congrArg e (hspecializes _ _ (e.symm.continuous.specialization_monotone hxy))
    rwa [← heq]
  have himage_closed : IsClosed (e '' (W : Set X)) :=
    PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible
      himage_stable ((hW.image e.continuous).isConstructible (e.isOpenMap _ W.isOpen))
  have hclosed : IsClosed (W : Set X) := by
    rw [← Set.preimage_image_eq (W : Set X) e.injective]
    exact himage_closed.preimage e.continuous
  refine ⟨hclosed, ?_⟩
  let : IsAffineHom W.ι :=
    isAffineHom_of_isInducing W.ι W.isOpenEmbedding.isInducing (by
      simpa [Scheme.Opens.range_ι] using hclosed)
  exact isAffine_of_isAffineHom W.ι

/-- A quasi-compact open of a zero-dimensional scheme which is contained in an affine open `A` is
itself an affine open, and it is closed as a subset of `A`. -/
private lemma isAffineOpen_and_isClosed_of_isCompact_of_le {X : Scheme.{u}}
    (hX : topologicalKrullDim X = 0) {A W : X.Opens} (hA : IsAffineOpen A)
    (hW : IsCompact (W : Set X)) (hWA : W ≤ A) :
    IsAffineOpen W ∧ IsClosed ((A.ι ⁻¹ᵁ W : A.toScheme.Opens) : Set A.toScheme) := by
  classical
  cases isEmpty_or_nonempty A.toScheme with
  | inl _ =>
      have hbot : W = ⊥ :=
        le_bot_iff.mp fun x hx ↦ isEmptyElim (α := A.toScheme) ⟨x, hWA hx⟩
      rw [hbot]
      exact ⟨isAffineOpen_bot _, by simp⟩
  | inr hne =>
      let : IsAffine A.toScheme := hA
      have hdim : topologicalKrullDim A.toScheme = 0 :=
        topologicalKrullDim_eq_zero_of_nonempty_of_le hne
          ((topologicalKrullDim_subspace_le X (A : Set X)).trans hX.le)
      have hpre : IsCompact (A.ι ⁻¹ᵁ W : Set A.toScheme) :=
        A.ι.isOpenEmbedding.isInducing.isCompact_preimage' hW fun x hx ↦ ⟨⟨x, hWA hx⟩, rfl⟩
      obtain ⟨hclosed, haff⟩ :=
        isClosed_and_isAffineOpen_of_isCompact_of_isAffine A.toScheme hdim (A.ι ⁻¹ᵁ W) hpre
      refine ⟨?_, hclosed⟩
      simpa [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hWA] using
        A.ι.isAffineOpen_iff_of_isOpenImmersion.mpr haff

/-- If the intersection of two affine opens is affine and closed in the first of them, then the
tensor product of their rings of sections surjects onto the sections of the intersection. -/
public lemma sectionTensorMap_surjective_of_isClosed_inf
    (X : Scheme.{u}) {U V : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen (U ⊓ V))
    (hclosed : IsClosed ((U.ι ⁻¹ᵁ (U ⊓ V) : U.toScheme.Opens) : Set U.toScheme)) :
    Function.Surjective (sectionTensorMap X U V) := by
  classical
  let W : X.Opens := U ⊓ V
  let g := X.homOfLE (U := W) (V := U) (inf_le_left : W ≤ U)
  let : IsAffine U.toScheme := hU
  let : IsAffine W.toScheme := hW
  have hgclosed : IsClosed (Set.range g) := by
    show IsClosed (g.opensRange : Set U.toScheme)
    rwa [Scheme.opensRange_homOfLE]
  let : IsClosedImmersion g := IsClosedImmersion.of_isPreimmersion g hgclosed
  have hgsurj : Function.Surjective g.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  have hrestrict : Function.Surjective
      ((X.presheaf.map (homOfLE inf_le_left).op).hom : Γ(X, U) → Γ(X, W)) := by
    have hLE : W ≤ (𝟙 X) ⁻¹ᵁ U := inf_le_left
    let r := Scheme.Hom.resLE (𝟙 X) U W hLE
    have hr : r = g := by
      dsimp [r, g]
      rw [show hLE = (inf_le_left : W ≤ U) from Subsingleton.elim _ _, Scheme.Hom.resLE_id]
    have hrsurj : Function.Surjective r.appTop := by simpa [hr] using hgsurj
    let e := arrowResLEAppIso (𝟙 X) U W hLE
    have happLE : Function.Surjective (Scheme.Hom.appLE (𝟙 X) U W hLE) := by
      intro b
      obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso e.hom.right).2 b
      obtain ⟨a, ha⟩ := hrsurj c
      refine ⟨e.hom.left a, ?_⟩
      have hcomm := Arrow.w e.hom
      change e.hom.left ≫ Scheme.Hom.appLE (𝟙 X) U W hLE = r.appTop ≫ e.hom.right at hcomm
      have hpoint := congrArg (fun k : Γ(U, ⊤) ⟶ Γ(X, W) ↦ k.hom a) hcomm
      simpa only [ConcreteCategory.comp_apply, ha, hc] using hpoint
    have happ : (Scheme.Hom.appLE (𝟙 X) U W hLE).hom =
        (X.presheaf.map (homOfLE inf_le_left).op).hom := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      congr 1
    simpa [happ] using happLE
  intro s
  obtain ⟨a, ha⟩ := hrestrict s
  exact ⟨a ⊗ₜ[ℤ] (1 : Γ(X, V)), by simp [sectionTensorMap, ha]⟩

/-- An affine open of a zero-dimensional scheme has Hausdorff underlying space. -/
private lemma t2Space_of_isAffineOpen_of_topologicalKrullDim_eq_zero (X : Scheme.{u})
    (hX : topologicalKrullDim X = 0) (U : X.Opens) (hU : IsAffineOpen U) :
    T2Space U.toScheme := by
  classical
  let : IsAffine U.toScheme := hU
  have hdimSpec : topologicalKrullDim (Spec Γ(X, U)) ≤ 0 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_subspace_le X (U : Set X)).trans hX.le
  have hle : Order.krullDim (PrimeSpectrum Γ(X, U)) ≤ 0 := by
    show ringKrullDim Γ(X, U) ≤ 0
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hdimSpec
  have hmax : ∀ p : PrimeSpectrum Γ(X, U), IsMax p :=
    Order.krullDim_nonpos_iff_forall_isMax.mp hle
  have hno : ∀ p q : Ideal Γ(X, U), p.IsPrime → q.IsPrime → p ≤ q → p = q := fun p q hp hq hpq ↦
    congrArg PrimeSpectrum.asIdeal
      ((hmax (⟨p, hp⟩ : PrimeSpectrum Γ(X, U))).eq_of_le (show _ ≤ (⟨q, hq⟩ : _) from hpq))
  let : T2Space (Spec Γ(X, U)) := ((spec_profinite_tfae Γ(X, U)).out 5 2).mp hno
  exact hU.isoSpec.hom.homeomorph.symm.t2Space

/-- **Stacks Project, Tag 0CKV.** For a scheme of dimension zero, quasi-separatedness,
separatedness, Hausdorffness of the underlying space, and closedness of every affine open are
equivalent. -/
@[stacks 0CKV "separation_equivalences"]
theorem separation_tfae_of_topologicalKrullDim_eq_zero (X : Scheme.{u})
    (hX : topologicalKrullDim X = 0) :
    List.TFAE [
      QuasiSeparatedSpace X,
      X.IsSeparated,
      T2Space X,
      ∀ U : X.Opens, IsAffineOpen U → IsClosed (U : Set X)] := by
  classical
  have hex (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
    exact ⟨U, hU, hxU⟩
  tfae_have 1 → 2 := by
    intro hqs
    refine ⟨isSeparated_of_affine_intersections (terminal.from X) fun x y _ ↦ ?_⟩
    obtain ⟨U, hU, hxU⟩ := hex x
    obtain ⟨V, hV, hyV⟩ := hex y
    obtain ⟨hW, hclosed⟩ := isAffineOpen_and_isClosed_of_isCompact_of_le hX hU
      (quasiSeparatedSpace_iff_forall_affineOpens.mp hqs ⟨U, hU⟩ ⟨V, hV⟩) inf_le_left
    exact ⟨U, V, ⊤, hxU, hyV, hU, hV, isAffineOpen_top _, by simp, by simp, hW,
      sectionTensorMap_surjective_of_isClosed_inf X hU hW hclosed⟩
  tfae_have 2 → 3 := by
    intro hsep
    refine ⟨fun x y hxy ↦ ?_⟩
    obtain ⟨U, hU, hxU⟩ := hex x
    by_cases hyU : y ∈ U
    · obtain ⟨A, B, hAo, hBo, hxA, hyB, hAB⟩ :=
        (t2Space_of_isAffineOpen_of_topologicalKrullDim_eq_zero X hX U hU).t2
          (show (⟨x, hxU⟩ : U.toScheme) ≠ ⟨y, hyU⟩ from fun h ↦ hxy (congrArg Subtype.val h))
      refine ⟨U.ι '' A, U.ι '' B, U.ι.isOpenEmbedding.isOpenMap A hAo,
        U.ι.isOpenEmbedding.isOpenMap B hBo, ⟨⟨x, hxU⟩, hxA, rfl⟩, ⟨⟨y, hyU⟩, hyB, rfl⟩, ?_⟩
      rw [Set.disjoint_left]
      rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      exact (Set.disjoint_left.mp hAB) ha (U.ι.isOpenEmbedding.injective hab.symm ▸ hb)
    · obtain ⟨V, hV, hyV⟩ := hex y
      let : X.IsSeparated := hsep
      obtain ⟨-, hclosed⟩ := isAffineOpen_and_isClosed_of_isCompact_of_le hX hV
        (hV.inf hU).isCompact (inf_le_left : V ⊓ U ≤ V)
      refine ⟨U, V.ι '' ((V.ι ⁻¹ᵁ (V ⊓ U) : Set V.toScheme)ᶜ), U.2,
        V.ι.isOpenEmbedding.isOpenMap _ hclosed.isOpen_compl, hxU, ⟨⟨y, hyV⟩, ?_, rfl⟩, ?_⟩
      · intro hy
        exact hyU (by simpa using (show V.ι ⟨y, hyV⟩ ∈ V ⊓ U from hy).2)
      · rw [Set.disjoint_left]
        rintro z hzU ⟨w, hw, rfl⟩
        exact hw (show V.ι w ∈ V ⊓ U from ⟨w.2, hzU⟩)
  tfae_have 3 → 4 := fun _ U hU ↦ hU.isCompact.isClosed
  tfae_have 4 → 1 := by
    intro hclosed
    refine quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V ↦ ?_
    exact U.2.isCompact.of_isClosed_subset ((hclosed U.1 U.2).inter (hclosed V.1 V.2))
      fun x hx ↦ hx.1
  tfae_finish

/-- Every affine open of a quasi-separated zero-dimensional scheme is closed. -/
private lemma isClosed_of_isAffineOpen_of_topologicalKrullDim_eq_zero (X : Scheme.{u})
    [QuasiSeparatedSpace X] (hX : topologicalKrullDim X = 0) {U : X.Opens} (hU : IsAffineOpen U) :
    IsClosed (U : Set X) :=
  ((separation_tfae_of_topologicalKrullDim_eq_zero X hX).out 1 4 rfl rfl).mp inferInstance U hU

/-- **Stacks Project, Tag 0CKV.** The connected components of a quasi-separated zero-dimensional
scheme are its points. -/
@[stacks 0CKV "connected_components"]
theorem connectedComponent_eq_singleton_of_topologicalKrullDim_eq_zero (X : Scheme.{u})
    [QuasiSeparatedSpace X] (hX : topologicalKrullDim X = 0) (x : X) :
    connectedComponent x = {x} := by
  classical
  let : T2Space X :=
    ((separation_tfae_of_topologicalKrullDim_eq_zero X hX).out 1 3 rfl rfl).mp inferInstance
  refine Set.Subset.antisymm (fun y hy ↦ ?_) fun y hy ↦ Set.mem_singleton_iff.mp hy ▸
    mem_connectedComponent
  by_cases hxy : x = y
  · simp [hxy]
  obtain ⟨W, hWaffine, hxW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x)
      (U := ⟨({y} : Set X)ᶜ, isClosed_singleton.isOpen_compl⟩) (by simpa using hxy)
  exact absurd (IsClopen.connectedComponent_subset (s := (W : Set X))
      ⟨isClosed_of_isAffineOpen_of_topologicalKrullDim_eq_zero X hX hWaffine, W.2⟩ hxW hy)
    fun hyW ↦ by simpa using hWU hyW

/-- A quasi-compact open of a quasi-separated zero-dimensional scheme which is the union of two
affine opens is affine. -/
private lemma isAffineOpen_of_isCompact_of_eq_sup (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (hX : topologicalKrullDim X = 0) {A B : X.Opens} (hA : IsAffineOpen A)
    (hB : IsAffineOpen B) {K : X.Opens} (hK : IsCompact (K : Set X))
    (hAB : K = A ⊔ B) : IsAffineOpen K := by
  classical
  have hcompl (C : X.Opens) (hC : IsAffineOpen C) : ((Cᶜ : X.Opens) : Set X) = (C : Set X)ᶜ := by
    rw [Opens.coe_compl_eq_interior_compl, interior_eq_iff_isOpen.mpr
      (isClosed_of_isAffineOpen_of_topologicalKrullDim_eq_zero X hX hC).isOpen_compl]
  have key (C D : X.Opens) (hC : IsAffineOpen C) (hD : IsClosed (D : Set X)) (h : C ⊓ D ≤ K) :
      IsAffineOpen (C ⊓ D) :=
    (isAffineOpen_and_isClosed_of_isCompact_of_le hX hC (hK.of_isClosed_subset
      ((isClosed_of_isAffineOpen_of_topologicalKrullDim_eq_zero X hX hC).inter hD) h)
      inf_le_left).1
  have hclosedA := isClosed_of_isAffineOpen_of_topologicalKrullDim_eq_zero X hX hA
  have hclosedB := isClosed_of_isAffineOpen_of_topologicalKrullDim_eq_zero X hX hB
  have hcomplA := hcompl A hA
  have hcomplB := hcompl B hB
  have hA₀ : IsAffineOpen (A ⊓ Bᶜ) :=
    key A Bᶜ hA (by rw [hcomplB]; exact B.2.isClosed_compl)
      (by rw [hAB]; exact fun x hx ↦ Or.inl hx.1)
  have hI : IsAffineOpen (A ⊓ B) := key A B hA hclosedB (by rw [hAB]; exact inf_le_sup)
  have hB₀ : IsAffineOpen (B ⊓ Aᶜ) :=
    key B Aᶜ hB (by rw [hcomplA]; exact A.2.isClosed_compl)
      (by rw [hAB]; exact fun x hx ↦ Or.inr hx.1)
  have hd : Disjoint (A ⊓ Bᶜ) (A ⊓ B) ∧ Disjoint (A ⊓ Bᶜ) (B ⊓ Aᶜ) ∧
      Disjoint (A ⊓ B) (B ⊓ Aᶜ) := by
    refine ⟨?_, ?_, ?_⟩ <;>
      (rw [disjoint_iff]; ext x; simp [hcomplA, hcomplB]; tauto)
  have hab := IsAffineOpen.sup_of_disjoint (hA₀.sup_of_disjoint hI hd.1) hB₀
    (by rw [disjoint_sup_left]; exact ⟨hd.2.1, hd.2.2⟩)
  rw [hAB]
  convert hab using 1
  ext x
  simp [hcomplA, hcomplB]
  tauto

/-- A quasi-compact open of a quasi-separated zero-dimensional scheme which is the union of a
finite family of affine opens is affine. -/
private lemma isAffineOpen_of_isCompact_of_eq_biSup (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (hX : topologicalKrullDim X = 0) {s : Set X.affineOpens} (hs : s.Finite)
    {K : X.Opens} (hK : IsCompact (K : Set X))
    (hKs : K = ⨆ i ∈ s, (i : X.Opens)) : IsAffineOpen K := by
  revert K hK
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      intro K hK hKs
      rw [hKs]
      exact IsAffineOpen.of_subsingleton (by simp)
  | @insert A s hA hs ih =>
      intro K hK hKs
      let V : X.Opens := ⨆ i ∈ s, (i : X.Opens)
      have hprev : IsCompact (V : Set X) := by
        refine hK.of_isClosed_subset ?_ ?_
        · simpa [V] using hs.isClosed_biUnion fun i _ ↦
          isClosed_of_isAffineOpen_of_topologicalKrullDim_eq_zero X hX i.2
        · show V ≤ K
          rw [hKs]
          exact iSup_le fun i ↦ iSup_le fun hi ↦
            le_iSup_of_le i (le_iSup_of_le (Set.mem_insert_of_mem A hi) le_rfl)
      refine isAffineOpen_of_isCompact_of_eq_sup X hX (ih hprev rfl) A.2 hK ?_
      rw [hKs]
      ext x
      simp [V, or_comm]

/-- **Stacks Project, Tag 0CKV.** Every quasi-compact open subset of a quasi-separated scheme of
dimension zero is affine. -/
@[stacks 0CKV "quasicompact_open_affine"]
theorem isAffineOpen_of_isCompact_of_topologicalKrullDim_eq_zero (X : Scheme.{u})
    [QuasiSeparatedSpace X] (hX : topologicalKrullDim X = 0) (U : X.Opens)
    (hU : IsCompact (U : Set X)) : IsAffineOpen U := by
  obtain ⟨s, hs, hUs⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  exact isAffineOpen_of_isCompact_of_eq_biSup X hX hs hU hUs

/-- **Stacks Project, Tag 0CKV.** A quasi-compact, quasi-separated scheme of dimension zero is
affine. -/
@[stacks 0CKV "quasicompact_affine"]
theorem isAffine_of_topologicalKrullDim_eq_zero (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (hX : topologicalKrullDim X = 0) : IsAffine X := by
  let : IsAffine (⊤ : X.Opens) :=
    isAffineOpen_of_isCompact_of_topologicalKrullDim_eq_zero X hX ⊤ isCompact_univ
  exact IsAffine.of_isIso X.topIso.inv

end AlgebraicGeometry

end
