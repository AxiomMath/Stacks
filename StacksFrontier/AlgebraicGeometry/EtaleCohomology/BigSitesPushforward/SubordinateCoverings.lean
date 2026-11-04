module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesPushforward.ClosedImmersionCoverings
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings

/-!
# Coverings adapted to a closed immersion

Given a closed immersion and a syntomic, smooth, or étale covering of its source, the target
admits a covering of the same kind whose members either miss the source or, after base change,
factor through a member of the original covering.

## Main results

* `AlgebraicGeometry.exists_syntomicCovering_subordinate_to_closedImmersion` gives the syntomic
  case.
* `AlgebraicGeometry.exists_smoothCovering_subordinate_to_closedImmersion` gives the smooth
  case.
* `AlgebraicGeometry.exists_etaleCovering_subordinate_to_closedImmersion` gives the étale case.

## Implementation notes

The three alternatives in the source are stated separately. An empty base change is expressed
by `IsEmpty`; otherwise the factorization is an equality of morphisms to the source of the
closed immersion. The smooth and étale coverings use Mathlib's precoverages, and the syntomic
covering uses the predicate of Tag 0225.

All three go through one construction: lift each member of the given covering along the closed
immersion, and add the open complement of the closed subscheme to cover the rest of the target.
The complement is an open immersion, which is why each of the three properties is only required
to contain the open immersions.

## References

* [Stacks Project, Tag 04E4](https://stacks.math.columbia.edu/tag/04E4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MorphismProperty

universe u v

namespace AlgebraicGeometry


private theorem zariskiCover_surjective {S : Scheme.{u}} {I : Type u}
    {V : I → Scheme.{u}} {p : ∀ i, V i ⟶ S}
    (h : Presieve.ofArrows V p ∈ Scheme.zariskiPrecoverage S) :
    ∀ z : S, ∃ i w, p i w = z :=
  ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).mp
    (by simpa [Scheme.zariskiPrecoverage] using h)).1

private theorem extendCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {I : Type v} (U : I → Scheme.{u}) (p : ∀ i, U i ⟶ X)
    (P : MorphismProperty Scheme.{u})
    (hopen : ∀ {A B : Scheme.{u}} (g : A ⟶ B), IsOpenImmersion g → P g)
    (hsource : ∀ x : X, ∃ i z, p i z = x)
    (hlocal : ∀ i, ∃ (Ji : Type u) (Vi : Ji → Scheme.{u})
      (qi : ∀ j, Vi j ⟶ Y) (gi : ∀ j, pullback (qi j) f ⟶ U i),
        (∀ j, P (qi j)) ∧
        (∀ j, gi j ≫ p i = pullback.snd (qi j) f) ∧
        Presieve.ofArrows (fun j => pullback (qi j) f) gi ∈ Scheme.zariskiPrecoverage (U i)) :
    ∃ (J : Type (max u v)) (V : J → Scheme.{u}) (q : ∀ j, V j ⟶ Y),
      (∀ j, P (q j)) ∧ (∀ y : Y, ∃ j z, q j z = y) ∧
        ∀ j, (IsEmpty (pullback (q j) f : Scheme.{u}) ∨
          ∃ i, ∃ h : pullback (q j) f ⟶ U i,
            h ≫ p i = pullback.snd (q j) f) := by
  classical
  choose Ji Vi qi gi hPi hfaci hcovi using hlocal
  let W : Y.Opens := ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let J : Type (max u v) := (Σ i, Ji i) ⊕ Unit
  let V : J → Scheme.{u} := fun j => match j with
    | Sum.inl a => Vi a.1 a.2
    | Sum.inr _ => W.toScheme
  let q : ∀ j, V j ⟶ Y := fun j => match j with
    | Sum.inl a => qi a.1 a.2
    | Sum.inr _ => W.ι
  refine ⟨J, V, q, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | inl a => exact hPi a.1 a.2
    | inr _ => exact hopen W.ι inferInstance
  · intro y
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨i, z, hzi⟩ := hsource x
      obtain ⟨j, w, hgw⟩ := zariskiCover_surjective (hcovi i) z
      refine ⟨Sum.inl ⟨i, j⟩, pullback.fst (qi i j) f w, ?_⟩
      have hsnd : pullback.snd (qi i j) f w = x := by
        have h := congrArg (fun k : pullback (qi i j) f ⟶ X => k w) (hfaci i j)
        have h' : p i (gi i j w) = pullback.snd (qi i j) f w := by
          simpa only [← Scheme.Hom.comp_apply] using h
        rw [hgw] at h'
        exact h'.symm.trans hzi
      have hpull : qi i j (pullback.fst (qi i j) f w) = f (pullback.snd (qi i j) f w) := by
        have h := congrArg (fun k : pullback (qi i j) f ⟶ Y => k w)
          (pullback.condition (f := qi i j) (g := f))
        simpa only [← Scheme.Hom.comp_apply] using h
      exact hpull.trans (congrArg f hsnd)
    · refine ⟨Sum.inr Unit.unit, ⟨y, by simpa [W] using hy⟩, ?_⟩
      rfl
  · intro j
    cases j with
    | inl a => exact Or.inr ⟨a.1, gi a.1 a.2, hfaci a.1 a.2⟩
    | inr t =>
      apply Or.inl
      apply Scheme.isEmpty_pullback_iff.mpr
      apply Set.disjoint_left.mpr
      intro y hyQ hyF
      obtain ⟨x, rfl⟩ := hyF
      change f x ∈ Set.range W.ι at hyQ
      rw [Scheme.Opens.range_ι] at hyQ
      change f x ∈ (Set.range f)ᶜ at hyQ
      exact hyQ ⟨x, rfl⟩

/-- A syntomic covering of a closed subscheme can be prepared by a syntomic covering of the
ambient scheme, with each base-changed member empty or subordinate to the original covering. -/
@[stacks 04E4 "syntomic case"]
public theorem exists_syntomicCovering_subordinate_to_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {I : Type v} (U : I → Scheme.{u}) (p : ∀ i, U i ⟶ X)
    (hp : AlgebraicGeometry.IsSyntomicCovering U p) :
    ∃ (J : Type (max u v)) (V : J → Scheme.{u}) (q : ∀ j, V j ⟶ Y),
      AlgebraicGeometry.IsSyntomicCovering V q ∧
        ∀ j, (IsEmpty (pullback (q j) f : Scheme.{u}) ∨
          ∃ i, ∃ h : pullback (q j) f ⟶ U i,
            h ≫ p i = pullback.snd (q j) f) :=
  by
    classical
    have hsource : ∀ x : X, ∃ i z, p i z = x := by
      intro x
      have hx := Set.ext_iff.mp hp.2 x
      simpa only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true] using hx
    obtain ⟨J, V, q, hq, hcover, hfactor⟩ :=
      extendCover f U p (fun {A B} g => AlgebraicGeometry.Syntomic g)
        (fun g hg => AlgebraicGeometry.syntomic_of_isOpenImmersion g) hsource
        fun i => AlgebraicGeometry.exists_syntomic_zariskiCover_baseChange_of_isClosedImmersion
          f (p i) (hp.1 i)
    refine ⟨J, V, q, ⟨hq, ?_⟩, hfactor⟩
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact hcover y

/-- A smooth covering of a closed subscheme can be prepared by a smooth covering of the
ambient scheme, with each base-changed member empty or subordinate to the original covering. -/
@[stacks 04E4 "smooth case"]
public theorem exists_smoothCovering_subordinate_to_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {I : Type v} (U : I → Scheme.{u}) (p : ∀ i, U i ⟶ X)
    (hp : Presieve.ofArrows U p ∈ Scheme.precoverage (@Smooth.{u}) X) :
    ∃ (J : Type (max u v)) (V : J → Scheme.{u}) (q : ∀ j, V j ⟶ Y),
      Presieve.ofArrows V q ∈ Scheme.precoverage (@Smooth.{u}) Y ∧
        ∀ j, (IsEmpty (pullback (q j) f : Scheme.{u}) ∨
          ∃ i, ∃ h : pullback (q j) f ⟶ U i,
            h ≫ p i = pullback.snd (q j) f) :=
  by
    classical
    have hsrcmem := (Scheme.ofArrows_mem_precoverage_iff (P := @Smooth.{u})).mp hp
    obtain ⟨J, V, q, hq, hcover, hfactor⟩ :=
      extendCover f U p (@Smooth.{u}) (fun _ hg => inferInstance) hsrcmem.1
        fun i => have : Smooth (p i) := hsrcmem.2 i
          AlgebraicGeometry.exists_smooth_zariskiCover_baseChange_of_isClosedImmersion f (p i)
    refine ⟨J, V, q, ?_, hfactor⟩
    exact (Scheme.ofArrows_mem_precoverage_iff (P := @Smooth.{u})).mpr ⟨hcover, hq⟩

/-- An étale covering of a closed subscheme can be prepared by an étale covering of the
ambient scheme, with each base-changed member empty or subordinate to the original covering. -/
@[stacks 04E4 "étale case"]
public theorem exists_etaleCovering_subordinate_to_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {I : Type v} (U : I → Scheme.{u}) (p : ∀ i, U i ⟶ X)
    (hp : Presieve.ofArrows U p ∈ Scheme.etalePrecoverage X) :
    ∃ (J : Type (max u v)) (V : J → Scheme.{u}) (q : ∀ j, V j ⟶ Y),
      Presieve.ofArrows V q ∈ Scheme.etalePrecoverage Y ∧
        ∀ j, (IsEmpty (pullback (q j) f : Scheme.{u}) ∨
          ∃ i, ∃ h : pullback (q j) f ⟶ U i,
            h ≫ p i = pullback.snd (q j) f) :=
  by
    classical
    have hsrcmem := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})).mp hp
    obtain ⟨J, V, q, hq, hcover, hfactor⟩ :=
      extendCover f U p (@Etale.{u}) (fun _ hg => inferInstance) hsrcmem.1
        fun i => have : Etale (p i) := hsrcmem.2 i
          AlgebraicGeometry.exists_etale_zariskiCover_baseChange_of_isClosedImmersion f (p i)
    refine ⟨J, V, q, ?_, hfactor⟩
    exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})).mpr ⟨hcover, hq⟩

end AlgebraicGeometry
