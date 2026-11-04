module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness

/-!
# The generic flatness stratification over a Noetherian base

Stacks 0H3Z says that a morphism of finite presentation `f : X ⟶ S` between quasi-compact and
quasi-separated schemes admits a stratification `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of its base by
closed subschemes cut out by finite type ideal sheaves, with `S₀ ⊆ S` a thickening, such that
`X ×_S (S_i ∖ S_{i+1})` is flat over the locally closed stratum `S_i ∖ S_{i+1}`. The conclusion
is `AlgebraicGeometry.HasFlatStratification`.

This file proves that statement when the base is Noetherian, which is the heart of the Stacks
argument: there the generic flatness of Stacks 052B produces, over the reduced induced structure
on any closed subset `C ⊆ S`, a dense open of `C` over which the base change of `f` is flat, and
the chain obtained by iterating `C ↦ C ∖ (that open)` terminates because a Noetherian space has
no infinite strictly descending chain of closed subsets. Over a Noetherian base the finite type
condition on the ideal sheaves is automatic.

What the *general* statement needs beyond this is absolute Noetherian approximation; that is
carried out in `StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationQcqs`, and the
general case is `AlgebraicGeometry.HasFlatStratification.of_finitePresentation`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_of_isLocallyNoetherian`: on a locally
  Noetherian scheme every quasi-coherent ideal sheaf is of finite type.
* `AlgebraicGeometry.exists_dense_open_flat_pullback_vanishingIdeal`: generic flatness over the
  reduced induced closed subscheme structure on a closed subset, in the form the stratification
  consumes — a dense open `U` of `C` with `X ×_S U` flat over `U`.
* `AlgebraicGeometry.exists_flat_strata_of_closeds`: the stratification induction, starting from
  an arbitrary closed subset of a Noetherian base.
* `AlgebraicGeometry.HasFlatStratification.of_isNoetherian`: **the Noetherian case of Stacks
  0H3Z**.

## Implementation notes

The stratum of the chain at `i` is the open subscheme `S_i ∖ S_{i+1}` of `S_i`, and what
`AlgebraicGeometry.HasFlatStratification` asks there is flatness of
`pullback.snd f (U.ι ≫ Z.subschemeι)`, whereas Stacks 052B — applied to the base change
`pullback.snd f Z.subschemeι` of `f` to the closed subscheme `Z` — delivers flatness of a
*restriction* of that base change to an open of `Z`. The two are identified by
`AlgebraicGeometry.flat_pullback_comp_of_flat_resLE`, which composes Mathlib's
`AlgebraicGeometry.pullbackLeftPullbackSndIso` (pullback along a composite is an iterated
pullback) with `AlgebraicGeometry.pullbackRestrictIsoRestrict` (pullback along an open immersion
is a restriction); flatness then transfers because an isomorphism is flat and flatness is stable
under composition. This is the identification named as outstanding in the module documentation of
`StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratification`.

The induction is a `WellFoundedLT` induction on `TopologicalSpace.Closeds S` rather than a use of
`Stacks.GenericFlatness.exists_strata`: the chain produced here has to carry the *flatness* datum
at each step alongside the closed sets, and the abstract assignment `Closeds S → Opens S` that
`exists_strata` takes would have to be chosen by `Classical.choice` and then re-opened at every
index, whereas the direct induction records the ideal sheaf chain and its flatness clauses
together.

Strata are given the *reduced* induced closed subscheme structure, i.e. the subscheme cut out by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, because Stacks 052B requires a reduced
base. This is also what makes the thickening clause come out: the first ideal sheaf of the chain
is `vanishingIdeal ⊤ = S.nilradical`, which is supported on all of `S`.

## How the general statement follows

The Stacks proof of 0ASY (of which 0H3Z is the case `ℱ = 𝒪_X`) reduces the quasi-compact
quasi-separated case to the Noetherian case proved here by absolute Noetherian approximation:
one writes `f` as a base change of a morphism of schemes of finite type over `ℤ`. That reduction
is `AlgebraicGeometry.exists_flat_stratification`, and the resulting general form of the
statement below is `AlgebraicGeometry.HasFlatStratification.of_finitePresentation`, in
`StacksFrontier.AlgebraicGeometry.GenericFlatness.MorphismFlatStratificationQcqs`.

## References

* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme every quasi-coherent ideal sheaf is of finite type: its ideal
on an affine open is an ideal of a Noetherian ring. -/
theorem Scheme.IdealSheafData.isFiniteType_of_isLocallyNoetherian {S : Scheme.{u}}
    [IsLocallyNoetherian S] (I : S.IdealSheafData) : I.IsFiniteType := fun U ↦
  have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian U
  Ideal.fg_of_isNoetherianRing _

/-- **The strata of a flat stratification cover the first closed subscheme of the chain.** Every
point of `S_0` lies in exactly the locally closed stratum `S_i ∖ S_{i+1}` for which `i` is least
with `s ∉ S_{i+1}`.

This records that the conclusion `AlgebraicGeometry.HasFlatStratification` is not satisfiable by a
chain whose strata are empty: since the thickening clause forces `(I 0).support = ⊤`, the strata
of any flat stratification cover the whole base, so the flatness clauses are assertions about
every point of `S`. Only `I (Fin.last t) = ⊤` is needed. -/
theorem Scheme.IdealSheafData.exists_mem_support_notMem_support {S : Scheme.{u}} {t : ℕ}
    (I : Fin (t + 1) → S.IdealSheafData) (hlast : I (Fin.last t) = ⊤) {s : S}
    (hs : s ∈ (I 0).support) :
    ∃ i : Fin t, s ∈ (I i.castSucc).support ∧ s ∉ (I i.succ).support := by
  induction t with
  | zero =>
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, hlast, support_top] at hs
    exact absurd hs (Set.notMem_empty s)
  | succ t ih =>
    by_cases h1 : s ∈ (I (0 : Fin (t + 1)).succ).support
    · obtain ⟨i, hi, hi'⟩ := ih (fun k ↦ I k.succ) (by rw [Fin.succ_last]; exact hlast) h1
      exact ⟨i.succ, by rwa [← Fin.succ_castSucc], hi'⟩
    · exact ⟨0, by rwa [Fin.castSucc_zero], h1⟩

/-- **Every point of the base lies in a stratum of a flat stratification.** The thickening clause
of `AlgebraicGeometry.HasFlatStratification` forces `(I 0).support = ⊤`, so the locally closed
strata `S_i ∖ S_{i+1}` cover `S`, and in particular none of them can be empty unless `S` is.

This is the non-vacuity guard on the conclusion: a chain whose flatness clauses were all about
empty strata could not satisfy both the thickening clause and `I (Fin.last t) = ⊤`. -/
theorem Scheme.IdealSheafData.exists_mem_stratum_of_isThickening {S : Scheme.{u}} {t : ℕ}
    (I : Fin (t + 1) → S.IdealSheafData)
    (h0 : Stacks.Thickenings.IsThickening (I 0).subschemeι) (hlast : I (Fin.last t) = ⊤)
    (s : S) : ∃ i : Fin t, s ∈ (I i.castSucc).support ∧ s ∉ (I i.succ).support :=
  exists_mem_support_notMem_support I hlast
    (((Scheme.IdealSheafData.isThickening_subschemeι_iff (I 0)).mp h0).ge trivial)

/-- Removing a dense open from a closed subset strictly shrinks it.

Given a closed embedding `i` of `T` into `S` with image the closed set `C`, and a dense open `U`
of `T`, the image of the complement of `U` is a closed set `D` strictly smaller than `C`, and `U`
is exactly the part of `T` lying outside `D`. This is the step of the stratification induction
that produces the next closed subset of the chain. -/
theorem exists_lt_closeds_of_dense_isOpen {T S : Type*} [TopologicalSpace T]
    [TopologicalSpace S] {i : T → S} (hi : Topology.IsClosedEmbedding i) (C : Closeds S)
    (hC : Set.range i = C) (U : Opens T) (hU : Dense (U : Set T)) (hC' : C ≠ ⊥) :
    ∃ D : Closeds S, D < C ∧ ∀ x : T, x ∈ U ↔ i x ∉ (D : Set S) := by
  have hDC : ∀ s ∈ i '' (U : Set T)ᶜ, s ∈ (C : Set S) := by
    rintro _ ⟨x, -, rfl⟩
    exact hC.le ⟨x, rfl⟩
  refine ⟨⟨i '' (U : Set T)ᶜ, hi.isClosedMap _ U.2.isClosed_compl⟩,
    lt_of_le_of_ne hDC fun hEq ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨y, hy⟩ : (C : Set S).Nonempty := by
      rcases Set.eq_empty_or_nonempty (C : Set S) with he | he
      · exact absurd (SetLike.coe_injective (he.trans Closeds.coe_bot.symm)) hC'
      · exact he
    obtain ⟨x, rfl⟩ := hC ▸ hy
    obtain ⟨z, hz⟩ := hU.nonempty_iff.mpr ⟨x⟩
    obtain ⟨w, hw, hwz⟩ : i z ∈ i '' (U : Set T)ᶜ := hEq.ge (hC.le ⟨z, rfl⟩)
    exact hw (hi.injective hwz ▸ hz)
  · refine ⟨fun hx ⟨w, hw, hwx⟩ ↦ hw (hi.injective hwx ▸ hx), fun hx ↦ ?_⟩
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩

/-- **Pullback along an open of a closed subscheme is a restriction of the pullback along the
closed subscheme.** If the base change of `f` to the closed subscheme cut out by `I` is flat over
an open `U` of that subscheme, then the base change of `f` to `U` itself is flat over `U`.

This identifies the morphism whose flatness `AlgebraicGeometry.HasFlatStratification` asserts on
a stratum with the restriction of the base changed morphism that Stacks 052B produces. -/
theorem flat_pullback_comp_of_flat_resLE {X S : Scheme.{u}} (f : X ⟶ S) {Z : Scheme.{u}}
    (i : Z ⟶ S) (U : Z.Opens)
    (h : Flat ((pullback.snd f i).resLE U ((pullback.snd f i) ⁻¹ᵁ U) le_rfl)) :
    Flat (pullback.snd f (U.ι ≫ i)) := by
  set p := pullback.snd f i with hp
  set W : (pullback f i).Opens := p ⁻¹ᵁ U with hW
  set q := p.resLE U W le_rfl with hq
  set e : pullback f (U.ι ≫ i) ≅ W.toScheme :=
    (pullbackLeftPullbackSndIso f i U.ι).symm ≪≫ pullbackRestrictIsoRestrict p U with he
  have key : e.hom ≫ q = pullback.snd f (U.ι ≫ i) := by
    refine (cancel_mono U.ι).1 ?_
    calc e.hom ≫ q ≫ U.ι
        = (pullbackLeftPullbackSndIso f i U.ι).inv ≫
            ((pullbackRestrictIsoRestrict p U).hom ≫ W.ι) ≫ p := by
          simp [he, hq, Scheme.Hom.resLE_comp_ι]
      _ = (pullbackLeftPullbackSndIso f i U.ι).inv ≫ pullback.fst p U.ι ≫ p := by
          rw [pullbackRestrictIsoRestrict_hom_ι]
      _ = pullback.snd f (U.ι ≫ i) ≫ U.ι := pullbackLeftPullbackSndIso_inv_fst_snd f i U.ι
  rw [← key]
  have : Flat q := h
  infer_instance

/-- **Generic flatness over a closed subset of the base.** Let `f : X ⟶ S` be quasi-compact and
locally of finite type and let `C ⊆ S` be closed, carrying the reduced induced closed subscheme
structure. Then there is a dense open `U` of `C` such that `X ×_S U` is flat over `U`.

This is Stacks 052H/052B applied to the base change of `f` to `C`, with the flatness transported
to the form the stratification of Stacks 0H3Z asks for. -/
theorem exists_dense_open_flat_pullback_vanishingIdeal {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (C : Closeds S) :
    ∃ U : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Opens,
      Dense (U : Set (Scheme.IdealSheafData.vanishingIdeal C).subscheme) ∧
      Flat (pullback.snd f (U.ι ≫ (Scheme.IdealSheafData.vanishingIdeal C).subschemeι)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal C with hI
  have : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
  set P := pullback f I.subschemeι with hP
  set F : P.Modules := SheafOfModules.unit P.ringCatSheaf with hF
  have : F.IsFiniteType := structureSheaf_isFiniteType P
  obtain ⟨U, hUdense, hflat, -⟩ :=
    exists_dense_open_flat_finitePresentation (pullback.snd f I.subschemeι) F
  exact ⟨U, hUdense, flat_pullback_comp_of_flat_resLE f I.subschemeι U hflat⟩

/-- **The stratification induction of Stacks 0ASY over a Noetherian base.** Every closed subset
`C` of a Noetherian base `S` is the top of a finite chain of closed subschemes
`C = S_0 ⊇ S_1 ⊇ ⋯ ⊇ S_t = ∅`, recorded by the ascending chain `I` of their ideal sheaves, each
of finite type, with `X ×_S (S_i ∖ S_{i+1})` flat over `S_i ∖ S_{i+1}`.

The chain starts at the *reduced* induced structure on `C`, which is what makes the clause
`I 0 = vanishingIdeal C` usable to produce the thickening clause of
`AlgebraicGeometry.HasFlatStratification` at `C = ⊤`. -/
theorem exists_flat_strata_of_closeds {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (C : Closeds S) :
    ∃ (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData),
      I 0 = Scheme.IdealSheafData.vanishingIdeal C ∧
      (∀ i, (I i).IsFiniteType) ∧
      (∀ i : Fin t, I i.castSucc ≤ I i.succ) ∧
      I (Fin.last t) = ⊤ ∧
      ∀ i : Fin t, Flat (pullback.snd f
        (((I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl).ι ≫
          (I i.castSucc).subschemeι)) := by
  induction C using WellFoundedLT.induction with
  | ind C ih =>
  by_cases hC : C = ⊥
  · subst hC
    exact ⟨0, fun _ ↦ ⊤, by simp, fun _ ↦
      Scheme.IdealSheafData.isFiniteType_of_isLocallyNoetherian ⊤, Fin.elim0, rfl, Fin.elim0⟩
  obtain ⟨U, hUdense, hUflat⟩ := exists_dense_open_flat_pullback_vanishingIdeal f C
  obtain ⟨D, hDC, hDU⟩ := exists_lt_closeds_of_dense_isOpen
    (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.isClosedEmbedding C
    (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C) U hUdense hC
  obtain ⟨t, I, hI0, hIFT, hIle, hItop, hIflat⟩ := ih D hDC
  have hopen : U = (Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹ᵁ
      (Scheme.IdealSheafData.vanishingIdeal D).support.compl := by
    ext x
    simpa [Scheme.IdealSheafData.coe_support_vanishingIdeal] using hDU x
  set I' : Fin (t + 2) → S.IdealSheafData := Fin.cons (Scheme.IdealSheafData.vanishingIdeal C) I
    with hI'
  have hzero : I' 0 = Scheme.IdealSheafData.vanishingIdeal C := Fin.cons_zero _ _
  have hsucc : ∀ j : Fin (t + 1), I' j.succ = I j := fun j ↦ Fin.cons_succ _ _ _
  refine ⟨t + 1, I', hzero, ?_, ?_, ?_, ?_⟩
  · refine Fin.cases ?_ fun j ↦ ?_
    · rw [hzero]
      exact Scheme.IdealSheafData.isFiniteType_of_isLocallyNoetherian _
    · simpa [hI'] using hIFT j
  · refine Fin.cases ?_ fun j ↦ ?_
    · simpa [hI', hI0] using Scheme.IdealSheafData.vanishingIdeal_antimono hDC.le
    · simpa [hI', ← Fin.succ_castSucc] using hIle j
  · simpa [hI', ← Fin.succ_last] using hItop
  · refine Fin.cases ?_ fun j ↦ ?_
    · rw [Fin.castSucc_zero, hzero, hsucc, hI0, ← hopen]
      exact hUflat
    · rw [← Fin.succ_castSucc, hsucc, hsucc]
      exact hIflat j

/-- **The Noetherian case of Stacks 0H3Z.** A quasi-compact morphism locally of finite type with
Noetherian target has a flat stratification of its base: there are closed subschemes
`S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`, each cut out by a finite type ideal sheaf, with `S₀ ⊆ S` a
thickening, such that `X ×_S (S_i ∖ S_{i+1})` is flat over `S_i ∖ S_{i+1}`.

The first closed subscheme is the reduction `S_red` of `S`, which is what makes it a thickening.

The hypotheses are weaker than those of Stacks 0H3Z in two ways, both forced by the proof rather
than chosen: the base is Noetherian, and `f` is only assumed quasi-compact and locally of finite
type rather than of finite presentation (over a Noetherian base the latter is implied). -/
theorem HasFlatStratification.of_isNoetherian {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] : HasFlatStratification f := by
  obtain ⟨t, I, hI0, hIFT, hIle, hItop, hIflat⟩ := exists_flat_strata_of_closeds f (⊤ : Closeds S)
  refine ⟨t, I, (Scheme.IdealSheafData.isThickening_subschemeι_iff _).mpr ?_,
    hIFT, hIle, hItop, hIflat⟩
  rw [hI0, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.support_nilradical]

/-- **The Noetherian case of Stacks 0H3Z**, with the hypotheses of the tag: a morphism of finite
presentation to a Noetherian base has a flat stratification. -/
@[stacks 0H3Z "the case of a Noetherian base. The general quasi-compact quasi-separated case \
of the tag is `AlgebraicGeometry.HasFlatStratification.of_finitePresentation`, which reduces to \
this one by absolute Noetherian approximation"]
theorem HasFlatStratification.of_finitePresentation_of_isNoetherian {X S : Scheme.{u}}
    [IsNoetherian S] (f : X ⟶ S) (hf : FinitePresentation f) : HasFlatStratification f :=
  have := hf.1
  have := hf.2.1
  .of_isNoetherian f

end AlgebraicGeometry

end
