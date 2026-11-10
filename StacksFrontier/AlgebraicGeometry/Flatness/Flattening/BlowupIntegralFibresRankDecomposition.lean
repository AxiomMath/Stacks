module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSeparation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresConstantRank
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresFlattening
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen

/-!
# Making the generic fibre rank constant by a blowup

The rank of `F` at the generic point of the fibre over a point of the distinguished open `U` need
not be the same at every point of `U`. The proof of [Stacks, Tag 0811] makes it constant: the
rank is locally constant on `U`, so `U` splits into finitely many disjoint quasi-compact opens on
which it is constant, and [Stacks, Tag 080P] produces a `U`-admissible blowup separating one of
those pieces from the others. Iterating reduces to the constant case.

## Main definitions

* `AlgebraicGeometry.FlatteningSituation.rankLocus`: the open of the total space where `F` is
  finite locally free of a given rank.
* `AlgebraicGeometry.FlatteningSituation.rankBase`: its image in the base, which is open because
  a flat morphism locally of finite presentation is universally open.
* `AlgebraicGeometry.FlatteningSituation.HasRankIn`: the ranks occurring at the generic points of
  the fibres over `U` all lie in a given finite set.

## Main results

* `AlgebraicGeometry.freeAtPointOfRank_of_fibre`: freeness of a fixed rank at one point of a
  fibre is freeness of that rank at any point of the fibre which is generic in it.
* `AlgebraicGeometry.FlatteningSituation.mem_rankBase_iff`: a point of the base lies in the
  rank-`a` image exactly when `F` is free of rank `a` near the generic point of its fibre.
* `AlgebraicGeometry.FlatteningSituation.isSolvable_of_hasRankIn`: **the reduction to the
  constant-rank case**, by induction on the number of occurring ranks.

## Implementation notes

That the rank function is locally constant on `U` is expressed through `rankBase`: the rank-`a`
locus of the total space is open because `AlgebraicGeometry.FreeAtPointOfRank` is an open
condition, and its image in the base is open because the structure morphism is flat and locally
of finite presentation, hence universally open. That a point of `U` lies in exactly one
`rankBase` is `AlgebraicGeometry.freeAtPointOfRank_unique` applied at the generic point of its
fibre, which exists because the fibres are geometrically integral.

Each of the two pieces of `U` is the difference of the quasi-compact `U` and the other, which is
open, hence quasi-compact; that is what [Stacks, Tag 080P] asks for. It returns an abstract
admissible blowup, from which `Stacks.Blowup.isAdmissibleBlowup_iff` extracts a centre together
with an isomorphism of its blowup with that scheme, along which the two clopen pieces are
transported.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Freeness of a fixed rank at a point of a fibre is freeness of that rank at any point of the
fibre which is generic in it.** The witness neighbourhood is open and contains a point of the
closure of the generic point, hence contains the generic point. -/
theorem freeAtPointOfRank_of_fibre {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x x' : X) (hx' : f.base x' = f.base x) (hgen : f.base ⁻¹' {f.base x} ⊆ closure {x})
    (a : ℕ) (h : FreeAtPointOfRank F x' a) : FreeAtPointOfRank F x a := by
  obtain ⟨W, hx'W, hdata⟩ := h
  refine ⟨W, ?_, hdata⟩
  obtain ⟨y, hyW, hy⟩ := mem_closure_iff.mp (hgen hx') (W : Set X) W.2 hx'W
  rw [Set.mem_singleton_iff] at hy
  exact hy ▸ hyW

namespace FlatteningSituation

variable (D : FlatteningSituation.{u})

/-! ### The rank loci -/

/-- The open locus of the total space where the module is finite locally free of rank `a`. -/
def rankLocus (a : ℕ) : D.X.Opens :=
  ⟨{x : D.X | FreeAtPointOfRank D.F x a}, isOpen_setOf_freeAtPointOfRank D.F a⟩

/-- The image in the base of the rank-`a` locus. It is open because the structure morphism, being
flat and locally of finite presentation, is universally open. -/
def rankBase (a : ℕ) : D.S.Opens :=
  have := D.finitePresentation.locallyOfFinitePresentation
  have : UniversallyOpen D.f := UniversallyOpen.of_flat D.f
  ⟨D.f.base '' (D.rankLocus a : Set D.X), D.f.isOpenMap _ (D.rankLocus a).2⟩

/-- **A point of the base lies in the rank-`a` image exactly when the module is finite locally
free of rank `a` near the generic point of its fibre.** -/
theorem mem_rankBase_iff (a : ℕ) (x : D.X)
    (hgen : D.f.base ⁻¹' {D.f.base x} ⊆ closure {x}) :
    D.f.base x ∈ D.rankBase a ↔ FreeAtPointOfRank D.F x a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨x, h, rfl⟩⟩
  obtain ⟨x', hx', hfx'⟩ := h
  exact freeAtPointOfRank_of_fibre D.f D.F x x' hfx' hgen a hx'

/-! ### The set of occurring ranks -/

/-- **The ranks occurring at the generic points of the fibres over the distinguished open all lie
in `A`.** -/
def HasRankIn (A : Finset ℕ) : Prop :=
  ∀ x : D.X, D.f.base x ∈ D.U → D.f.base ⁻¹' {D.f.base x} ⊆ closure {x} →
    ∀ r : ℕ, FreeAtPointOfRank D.F x r → r ∈ A

/-- **At most one rank occurs: the situation is solvable.** With no rank occurring the
distinguished open carries no generic point of a fibre at all, and the constant-rank case applies
with any value. -/
theorem isSolvable_of_card_le_one (A : Finset ℕ) (hcard : A.card ≤ 1) (hA : D.HasRankIn A) :
    D.IsSolvable := by
  by_cases hex : ∃ x : D.X, D.f.base x ∈ D.U ∧ D.f.base ⁻¹' {D.f.base x} ⊆ closure {x}
  · obtain ⟨x₀, h1, h2⟩ := hex
    obtain ⟨r, hr⟩ := D.free_at_generic x₀ h1 h2
    refine D.isSolvable_of_constantRank r fun x hx hgen ↦ ?_
    obtain ⟨r', hr'⟩ := D.free_at_generic x hx hgen
    have hrr : r' = r :=
      Finset.card_le_one.mp hcard r' (hA x hx hgen r' hr') r (hA x₀ h1 h2 r hr)
    exact hrr ▸ hr'
  · exact D.isSolvable_of_constantRank 0 fun x hx hgen ↦ absurd ⟨x, hx, hgen⟩ hex

/-! ### The point correspondence through a transform followed by a restriction -/

/-- **A generic point of a fibre over the distinguished open of a transformed-then-restricted
situation comes from such a point of the original situation**, lying over a prescribed point of
the open the restriction is taken over, with freeness of any rank transported. -/
theorem exists_point_of_restrict_transform (K : D.S.IdealSheafData)
    (hK : FinitePresentation K.subschemeι)
    (hKU : Disjoint (D.U : Set D.S) (K.support : Set D.S))
    (Z : (blowUp K).Opens) (hZ : IsCompact (Z : Set (blowUp K)))
    (z : ((D.transform K hK hKU).restrict Z hZ).X)
    (hz : ((D.transform K hK hKU).restrict Z hZ).f.base z ∈
      ((D.transform K hK hKU).restrict Z hZ).U)
    (hgen : ((D.transform K hK hKU).restrict Z hZ).f.base ⁻¹'
      {((D.transform K hK hKU).restrict Z hZ).f.base z} ⊆ closure {z}) :
    ∃ (x : D.X) (w : blowUp K), D.f.base x ∈ D.U ∧ w ∈ Z ∧
      D.f.base x = (blowUpToBase K).base w ∧
      D.f.base ⁻¹' {D.f.base x} ⊆ closure {x} ∧
      ∀ r : ℕ, FreeAtPointOfRank D.F x r →
        FreeAtPointOfRank ((D.transform K hK hKU).restrict Z hZ).F z r := by
  set D₂ := D.transform K hK hKU with hD₂
  obtain ⟨h1, h2, heq⟩ := D₂.mem_and_fibre_subset_closure_pullback Z z hz hgen
  obtain ⟨x, k1, k2, keq, k3⟩ := D.exists_point_of_strictTransform K
    ((pullback.fst D₂.f Z.ι).base z) h1 h2
  refine ⟨x, Z.ι.base ((pullback.snd D₂.f Z.ι).base z), k1,
    ((pullback.snd D₂.f Z.ι).base z).2, ?_, k2, fun r hr ↦ ?_⟩
  · rw [keq]
    exact congrArg (fun t ↦ (blowUpToBase K).base t) heq
  · exact freeAtPointOfRank_pullback (pullback.fst D₂.f Z.ι) D₂.F z r (k3 r hr)

/-! ### The reduction to a constant rank -/

/-- **The reduction to the constant-rank case.** If the ranks occurring at the generic points of
the fibres over the distinguished open lie in a finite set of at most `n` elements, the situation
is solvable. The induction separates one rank from the others by [Stacks, Tag 080P]. -/
theorem isSolvable_of_hasRankIn : ∀ (n : ℕ) (E : FlatteningSituation.{u}) (A : Finset ℕ),
    A.card ≤ n → E.HasRankIn A → E.IsSolvable := by
  intro n
  induction n with
  | zero => exact fun E A hcard hA ↦ E.isSolvable_of_card_le_one A (hcard.trans (by norm_num)) hA
  | succ n ih =>
    intro E A hcard hA
    classical
    by_cases hle : A.card ≤ 1
    · exact E.isSolvable_of_card_le_one A hle hA
    obtain ⟨a, haA⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    set Ua : E.S.Opens := E.U ⊓ E.rankBase a with hUa
    set Ur : E.S.Opens := E.U ⊓ ⨆ b : (A.erase a : Finset ℕ), E.rankBase (b : ℕ) with hUr
    -- Every point of the distinguished open is in exactly one of the two pieces.
    have hgenpt : ∀ u : E.S, u ∈ E.U → ∃ x : E.X, E.f.base x = u ∧
        E.f.base ⁻¹' {E.f.base x} ⊆ closure {x} := by
      intro u _
      obtain ⟨x, hxu, hxgen⟩ := exists_fibre_dense_preimage E.f u
      exact ⟨x, hxu, by rw [hxu]; exact hxgen⟩
    have hcover : (E.U : Set E.S) = (Ua : Set E.S) ∪ (Ur : Set E.S) := by
      refine Set.Subset.antisymm (fun u hu ↦ ?_) ?_
      · obtain ⟨x, hxu, hxgen⟩ := hgenpt u hu
        obtain ⟨r, hr⟩ := E.free_at_generic x (hxu ▸ hu) hxgen
        have hrA : r ∈ A := hA x (hxu ▸ hu) hxgen r hr
        by_cases hra : r = a
        · exact Or.inl ⟨hu, hxu ▸ (E.mem_rankBase_iff a x hxgen).mpr (hra ▸ hr)⟩
        · refine Or.inr ⟨hu, ?_⟩
          refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, Finset.mem_erase.mpr ⟨hra, hrA⟩⟩, ?_⟩
          exact hxu ▸ (E.mem_rankBase_iff r x hxgen).mpr hr
      · exact Set.union_subset (fun _ h ↦ h.1) fun _ h ↦ h.1
    have hdisj : Disjoint (Ua : Set E.S) (Ur : Set E.S) := by
      rw [Set.disjoint_left]
      rintro u ⟨hu, hua⟩ ⟨-, hur⟩
      obtain ⟨b, hub⟩ := TopologicalSpace.Opens.mem_iSup.mp hur
      obtain ⟨x, hxu, hxgen⟩ := hgenpt u hu
      have h1 : FreeAtPointOfRank E.F x a :=
        (E.mem_rankBase_iff a x hxgen).mp (by rw [hxu]; exact hua)
      have h2 : FreeAtPointOfRank E.F x (b : ℕ) :=
        (E.mem_rankBase_iff (b : ℕ) x hxgen).mp (by rw [hxu]; exact hub)
      exact (Finset.mem_erase.mp b.2).1 (freeAtPointOfRank_unique E.F h2 h1)
    have hcompact : ∀ P Q : E.S.Opens, Disjoint (P : Set E.S) (Q : Set E.S) →
        (E.U : Set E.S) = (P : Set E.S) ∪ (Q : Set E.S) → IsCompact (P : Set E.S) := by
      intro P Q hPQ hU
      have hd : (P : Set E.S) = (E.U : Set E.S) \ (Q : Set E.S) := by
        rw [hU, Set.union_sdiff_cancel_right (Set.disjoint_iff.mp hPQ)]
      rw [hd]
      exact E.compact_U.diff Q.2
    have hUac := hcompact Ua Ur hdisj hcover
    have hUrc := hcompact Ur Ua hdisj.symm (by rw [hcover, Set.union_comm])
    have hsup : Ua ⊔ Ur = E.U := by
      refine TopologicalSpace.Opens.ext ?_
      rw [TopologicalSpace.Opens.coe_sup, hcover]
    -- Tag 080P: a `U`-admissible blowup separating the two pieces.
    obtain ⟨S', bl, Z₁, Z₂, hadm, hZdisj, hZtop, hZ₁, hZ₂⟩ :=
      Stacks.Blowup.exists_admissibleBlowup_disjoint_open_cover E.S Ua Ur hUac hUrc
        (TopologicalSpace.Opens.coe_disjoint.mp hdisj)
    rw [hsup] at hadm
    obtain ⟨K, hKfp, hKU, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff E.U bl).mp hadm
    refine E.problem.isSolvable_of_transform K hKfp hKU (E.isSolvable_transform K hKfp hKU ?_)
    set E₂ := E.transform K hKfp hKU with hE₂
    set Z₁' : (blowUp K).Opens := e.inv ⁻¹ᵁ Z₁ with hZ₁'
    set Z₂' : (blowUp K).Opens := e.inv ⁻¹ᵁ Z₂ with hZ₂'
    have hZ'disj : Disjoint (Z₁' : Set (blowUp K)) (Z₂' : Set (blowUp K)) := by
      rw [Set.disjoint_left]
      intro w h1 h2
      exact (Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr hZdisj)) h1 h2
    have hZ'top : ∀ w : blowUp K, w ∈ Z₁' ∨ w ∈ Z₂' := by
      intro w
      have hm : e.inv.base w ∈ (Z₁ ⊔ Z₂ : S'.Opens) := by rw [hZtop]; trivial
      exact (TopologicalSpace.Opens.mem_sup).mp hm
    have hinv : ∀ w : blowUp K, bl.base (e.inv.base w) = (blowUpToBase K).base w := fun w ↦ by
      change (e.inv ≫ bl).base w = (blowUpToBase K).base w
      rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    have hpre : ∀ (V : E.S.Opens) (ZZ : S'.Opens), bl ⁻¹ᵁ V ≤ ZZ →
        blowUpToBase K ⁻¹ᵁ V ≤ e.inv ⁻¹ᵁ ZZ := by
      intro V ZZ hle w hw
      refine hle ?_
      change bl.base (e.inv.base w) ∈ V
      rw [hinv]
      exact hw
    have hZ₁p := hpre Ua Z₁ hZ₁
    have hZ₂p := hpre Ur Z₂ hZ₂
    -- Both pieces are quasi-compact: each is the complement of the other.
    have hclosed : ∀ (P Q : (blowUp K).Opens), Disjoint (P : Set (blowUp K)) (Q : Set (blowUp K)) →
        (∀ w : blowUp K, w ∈ P ∨ w ∈ Q) → IsCompact (P : Set (blowUp K)) := by
      intro P Q hpq hpqtop
      have : IsProper (blowUpToBase K) :=
        isProper_blowUpToBase_of_fg K ((finitePresentation_subschemeι_iff_isFiniteType K).mp hKfp)
      have : CompactSpace (blowUp K) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase K)
      have hP : (P : Set (blowUp K)) = (Q : Set (blowUp K))ᶜ := by
        refine Set.Subset.antisymm (fun w hw hwq ↦ (Set.disjoint_left.mp hpq) hw hwq) fun w hw ↦ ?_
        exact (hpqtop w).resolve_right hw
      rw [hP]
      exact (Q.2.isClosed_compl).isCompact
    have hZ₁c := hclosed Z₁' Z₂' hZ'disj hZ'top
    have hZ₂c := hclosed Z₂' Z₁' hZ'disj.symm fun w ↦ (hZ'top w).symm
    refine StrictTransformProblem.isSolvable_of_local E₂.problem
      (fun F hFP ↦ E₂.freeOnSurjectiveOpen_local F (by rw [hFP])) fun y ↦ ?_
    -- The base point of a generic fibre point over the first piece has rank `a`.
    have hcase₁ : (E₂.restrict Z₁' hZ₁c).IsSolvable := by
      refine (E₂.restrict Z₁' hZ₁c).isSolvable_of_constantRank a fun z hz hgen ↦ ?_
      obtain ⟨x, w, hxU, hwZ, hxw, hxgen, htr⟩ :=
        E.exists_point_of_restrict_transform K hKfp hKU Z₁' hZ₁c z hz hgen
      refine htr a ?_
      refine (E.mem_rankBase_iff a x hxgen).mp ?_
      have hUaU : E.f.base x ∈ (Ua : Set E.S) := by
        refine ((hcover ▸ hxU : E.f.base x ∈ (Ua : Set E.S) ∪ (Ur : Set E.S))).resolve_right
          fun hc ↦ ?_
        refine (Set.disjoint_left.mp hZ'disj) hwZ (hZ₂p ?_)
        change (blowUpToBase K).base w ∈ Ur
        rw [← hxw]
        exact hc
      exact hUaU.2
    -- Over the second piece the occurring ranks are the remaining ones.
    have hcase₂ : (E₂.restrict Z₂' hZ₂c).IsSolvable := by
      refine ih (E₂.restrict Z₂' hZ₂c) (A.erase a) ?_ fun z hz hgen r hr ↦ ?_
      · rw [Finset.card_erase_of_mem haA]
        omega
      obtain ⟨x, w, hxU, hwZ, hxw, hxgen, htr⟩ :=
        E.exists_point_of_restrict_transform K hKfp hKU Z₂' hZ₂c z hz hgen
      have hUrU : E.f.base x ∈ (Ur : Set E.S) := by
        refine ((hcover ▸ hxU : E.f.base x ∈ (Ua : Set E.S) ∪ (Ur : Set E.S))).resolve_left
          fun hc ↦ ?_
        refine (Set.disjoint_left.mp hZ'disj) (hZ₁p ?_) hwZ
        change (blowUpToBase K).base w ∈ Ua
        rw [← hxw]
        exact hc
      obtain ⟨b, hub⟩ := TopologicalSpace.Opens.mem_iSup.mp hUrU.2
      have hb : FreeAtPointOfRank E.F x (b : ℕ) :=
        (E.mem_rankBase_iff (b : ℕ) x hxgen).mp hub
      have : r = (b : ℕ) := freeAtPointOfRank_unique _ hr (htr (b : ℕ) hb)
      exact this ▸ b.2
    rcases hZ'top y with hy | hy
    · exact ⟨Z₁', hZ₁c, hy, E₂.isSolvable_restrict Z₁' hZ₁c hcase₁⟩
    · exact ⟨Z₂', hZ₂c, hy, E₂.isSolvable_restrict Z₂' hZ₂c hcase₂⟩

end FlatteningSituation

end AlgebraicGeometry

end
