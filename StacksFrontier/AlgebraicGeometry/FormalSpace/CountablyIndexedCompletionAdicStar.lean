module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedNotAdicStarSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# The formal completion along a countably indexed closed set (Stacks 0APW)

Let `X = Spec A` be an affine scheme over `S` and `T = V(I)` a closed subset. This file states
**Stacks 0APW** for the formal completion `X_{/T}` itself,
`AlgebraicGeometry.FormalSpace.zeroLocusCompletion`, with the countable indexedness of
**Stacks 0AIJ**, `AlgebraicGeometry.FormalSpace.IsCountablyIndexed`, as hypothesis.

The proof first turns countable indexedness of `X_{/T}` into what the Stacks proof says it
means: a decreasing sequence of ideals `J_n` with `V(J_n) = T`, cofinal among all ideals cutting
out `T`. It then identifies `X_{/T}` with the colimit of the `Spec (A ⧸ J_n)`, which is the
sheaf `AlgebraicGeometry.FormalSpace.countableCompletion` treated in
`StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedAdicStar.lean` and
`StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedNotAdicStarSheaf.lean`.

## Main results

* `AlgebraicGeometry.FormalSpace.countableCompletionIsoZeroLocusCompletion`: for a cofinal
  sequence `J` of ideals cutting out `V(I)`, the colimit of the `Spec (A ⧸ J_n)` is `X_{/V(I)}`.
* `AlgebraicGeometry.FormalSpace.exists_isCofinalVanishingSequence_of_isCountablyIndexed`: if
  `X_{/V(I)}` is countably indexed, there is such a cofinal sequence.
* `AlgebraicGeometry.FormalSpace.isAdicStar_zeroLocusCompletion_of_isCountablyIndexed`:
  **Stacks 0APW (1)**.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_not_isAdicStar_zeroLocusCompletion_gabber`:
  **Stacks 0APW (2)**.

## Implementation notes

The sequence is extracted from a presentation `X_{/T} ≅ colim_n Spec B_n` by factoring maps
between the two presentations of `X_{/T}`: each `Spec B_n` maps into some stage
`Spec (A ⧸ K_n)` of the presentation by all ideals with zero locus `T`, and each such stage
`Spec (A ⧸ L)` maps into some `Spec B_m`, both by
`AlgebraicGeometry.FormalSpace.exists_factor_to_affine_stage`. The composite
`Spec (A ⧸ L) ⟶ Spec (A ⧸ K_m)` lies over `Spec A`, so `K_m ≤ L`; the finite intersections of
the `K_n` are then the required sequence.

## References

* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0APW](https://stacks.math.columbia.edu/tag/0APW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits bigFppfOver_subcanonical

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A]
  (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)

/-! ### A cofinal sequence presents the completion -/

/-- The functor from the index of a cofinal sequence of ideals cutting out `V(I)` to the index of
all ideals cutting out `V(I)`. -/
abbrev cofinalSequenceIndex {I : Ideal A} (J : ℕ → Ideal A)
    (hJ : IsCofinalVanishingSequence A (PrimeSpectrum.zeroLocus (I : Set A)) J) :
    ULift.{u + 1} ℕ ⥤ SupportIndex I :=
  (show Monotone fun n : ULift.{u + 1} ℕ => (ULift.up (OrderDual.toDual
      (⟨J n.down, PrimeSpectrum.zeroLocus_eq_iff.mp (hJ.2.1 n.down)⟩ : SupportIdeal I)) :
        SupportIndex I) from
    fun _ _ h => antitone_nat_of_succ_le hJ.1 h).functor

/-- The index of a cofinal sequence is final in the index of all ideals with the same zero
locus. -/
theorem final_cofinalSequenceIndex {I : Ideal A} (J : ℕ → Ideal A)
    (hJ : IsCofinalVanishingSequence A (PrimeSpectrum.zeroLocus (I : Set A)) J) :
    (cofinalSequenceIndex J hJ).Final := by
  refine Monotone.final_functor_iff _ |>.mpr fun L => ?_
  obtain ⟨n, hn⟩ := hJ.2.2 L.down.1 (PrimeSpectrum.zeroLocus_eq_iff.mpr L.down.2)
  exact ⟨ULift.up n, hn⟩

/-- The diagram of quotient spectra of a cofinal sequence is the restriction of the diagram of
quotient spectra of all ideals with the same zero locus. -/
def countableNeighbourhoodDiagramIsoSupportDiagram (I : Ideal A) (J : ℕ → Ideal A)
    (hJ : IsCofinalVanishingSequence A (PrimeSpectrum.zeroLocus (I : Set A)) J) :
    countableNeighbourhoodDiagram B S hS f hA J hJ.1 ≅
      cofinalSequenceIndex J hJ ⋙ supportDiagram B S hS hA f I :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun g =>
    (Category.comp_id _).trans
      (Category.id_comp ((cofinalSequenceIndex J hJ ⋙ supportDiagram B S hS hA f I).map g)).symm)

/-- **The completion along a cofinal sequence is the formal completion.** If `J` is a
decreasing sequence of ideals cutting out `V(I)` and cofinal among the ideals cutting out
`V(I)`, the colimit of the `Spec (A ⧸ J n)` is the completion `X_{/V(I)}` of `X = Spec A`. -/
def countableCompletionIsoZeroLocusCompletion (I : Ideal A) (J : ℕ → Ideal A)
    (hJ : IsCofinalVanishingSequence A (PrimeSpectrum.zeroLocus (I : Set A)) J) :
    countableCompletion B S hS f hA J hJ.1 ≅ zeroLocusCompletion B S hS hA f I :=
  letI := final_cofinalSequenceIndex J hJ
  HasColimit.isoOfNatIso (Functor.isoWhiskerRight
      (countableNeighbourhoodDiagramIsoSupportDiagram B S hS hA f I J hJ)
      (BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ≪≫
    Functor.Final.colimitIso (cofinalSequenceIndex J hJ) (supportSheafDiagram B S hS hA f I) ≪≫
    (nonempty_iso_zeroLocusCompletion_colimit B S hS hA f I).some.symm

/-! ### A countably indexed completion has a cofinal sequence -/

/-- The cocone on the represented quotient stages with vertex the sheaf represented by
`Spec A`, given by the quotient maps. -/
def supportAffineCocone (I : Ideal A) : Cocone (supportSheafDiagram B S hS hA f I) where
  pt := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (affineOver B S hS hA f)
  ι :=
    { app K := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (supportStageToAffine B S hS hA f I K.down)
      naturality K L g := by
        simp only [Functor.const_obj_map]
        exact ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).symm.trans
          (congrArg (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            (supportStageToAffine_transition B S hS hA f I (supportIndex_le g))) }

/-- A morphism of quotient stages over `Spec A` reverses the inclusion of the ideals: if
`Spec (A ⧸ L) ⟶ Spec (A ⧸ K)` commutes with the quotient maps to `Spec A` then `K ≤ L`. -/
theorem le_of_comp_supportStageToAffine (I : Ideal A) {K L : SupportIdeal I}
    (g : (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I L) ⟶
      (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I K))
    (hg : g ≫ supportStageToAffine B S hS hA f I K = supportStageToAffine B S hS hA f I L) :
    K.1 ≤ L.1 := by
  have h := congrArg (BigFppfOver.toScheme B S hS).map hg
  rw [Functor.map_comp] at h
  let φ : Spec (.of (A ⧸ L.1)) ⟶ Spec (.of (A ⧸ K.1)) := (BigFppfOver.toScheme B S hS).map g
  change φ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L.1)) at h
  rw [← Spec.map_preimage φ, ← Spec.map_comp] at h
  have hr := Spec.map_injective h
  intro a ha
  have ha' := congrArg (fun r => r.hom a) hr
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at ha'
  exact Ideal.Quotient.eq_zero_iff_mem.mp ha'.symm

/-- If a stage of the presentation of `X_{/V(I)}` by all ideals cutting out `V(I)` maps into
another stage compatibly with the colimit inclusions, the ideals are reversely included. -/
theorem le_of_comp_colimit_ι (I : Ideal A) {K L : SupportIndex I}
    (g : (supportDiagram B S hS hA f I).obj L ⟶ (supportDiagram B S hS hA f I).obj K)
    (hg : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map g) ≫
          colimit.ι (supportSheafDiagram B S hS hA f I) K =
        colimit.ι (supportSheafDiagram B S hS hA f I) L) :
    K.down.1 ≤ L.down.1 := by
  have h := congrArg (· ≫ colimit.desc _ (supportAffineCocone B S hS hA f I)) hg
  simp only [Category.assoc, colimit.ι_desc] at h
  change _ ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (supportStageToAffine B S hS hA f I K.down) =
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (supportStageToAffine B S hS hA f I L.down) at h
  exact le_of_comp_supportStageToAffine B S hS hA f I _
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
      (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).trans h))

/-- The finite intersections `K 0 ⊓ ⋯ ⊓ K n` of a sequence of ideals. -/
def partialInfIdeal (K : ℕ → Ideal A) : ℕ → Ideal A
  | 0 => K 0
  | n + 1 => partialInfIdeal K n ⊓ K (n + 1)

/-- The `n`-th finite intersection lies in the `n`-th ideal. -/
theorem partialInfIdeal_le (K : ℕ → Ideal A) (n : ℕ) : partialInfIdeal K n ≤ K n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact inf_le_right

/-- The finite intersections decrease. -/
theorem partialInfIdeal_succ_le (K : ℕ → Ideal A) (n : ℕ) :
    partialInfIdeal K (n + 1) ≤ partialInfIdeal K n :=
  inf_le_left

/-- Finite intersections of ideals all cutting out `T` cut out `T`. -/
theorem zeroLocus_partialInfIdeal {T : Set (PrimeSpectrum A)} (K : ℕ → Ideal A)
    (hK : ∀ n, PrimeSpectrum.zeroLocus (K n : Set A) = T) (n : ℕ) :
    PrimeSpectrum.zeroLocus (partialInfIdeal K n : Set A) = T := by
  induction n with
  | zero => exact hK 0
  | succ n ih =>
    change PrimeSpectrum.zeroLocus ((partialInfIdeal K n ⊓ K (n + 1) : Ideal A) : Set A) = T
    rw [PrimeSpectrum.zeroLocus_inf, ih, hK, Set.union_self]

/-- **Countable indexedness of the completion, in terms of ideals.** If the completion
`X_{/V(I)}` of `X = Spec A` is countably indexed (Stacks 0AIJ), there is a decreasing sequence
of ideals cutting out `V(I)` which is cofinal among all ideals cutting out `V(I)`. This is the
first sentence of the proof of Stacks 0APW. -/
theorem exists_isCofinalVanishingSequence_of_isCountablyIndexed (I : Ideal A)
    (hX : IsCountablyIndexed B S hS (zeroLocusCompletion B S hS hA f I)) :
    ∃ J : ℕ → Ideal A,
      IsCofinalVanishingSequence A (PrimeSpectrum.zeroLocus (I : Set A)) J := by
  classical
  obtain ⟨D, hD, ⟨e⟩⟩ := hX
  let c := (nonempty_iso_zeroLocusCompletion_colimit B S hS hA f I).some
  have hA' : ∀ n : ℕ, ∃ (K : SupportIndex I)
      (k : D.obj n ⟶ (supportDiagram B S hS hA f I).obj K),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map k) ≫
        colimit.ι (supportSheafDiagram B S hS hA f I) K ≫ c.inv =
      colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) n ≫ e.inv := fun n =>
    exists_factor_to_affine_stage B S hS _ (SupportIndex I) (supportDiagram B S hS hA f I)
      (fun _ _ g => isThickening_supportDiagram_map B S hS hA f I g) c (D.obj n)
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) n ≫ e.inv)
  choose K k hk using hA'
  have hB : ∀ L : SupportIndex I, ∃ (m : ℕ)
      (h : (supportDiagram B S hS hA f I).obj L ⟶ D.obj m),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map h) ≫
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) m ≫ e.inv =
      colimit.ι (supportSheafDiagram B S hS hA f I) L ≫ c.inv := fun L =>
    exists_factor_to_affine_stage B S hS _ ℕ D hD e _
      (colimit.ι (supportSheafDiagram B S hS hA f I) L ≫ c.inv)
  have hcof : ∀ L : SupportIndex I, ∃ m, (K m).down.1 ≤ L.down.1 := by
    intro L
    obtain ⟨m, h, hh⟩ := hB L
    refine ⟨m, le_of_comp_colimit_ι B S hS hA f I (h ≫ k m) ?_⟩
    rw [← cancel_mono c.inv, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [hk m, hh]
  have hzero : ∀ n, PrimeSpectrum.zeroLocus ((K n).down.1 : Set A) =
      PrimeSpectrum.zeroLocus (I : Set A) := fun n =>
    PrimeSpectrum.zeroLocus_eq_iff.mpr (K n).down.2
  refine ⟨partialInfIdeal fun n => (K n).down.1, partialInfIdeal_succ_le _,
    zeroLocus_partialInfIdeal _ hzero, fun L hL => ?_⟩
  obtain ⟨m, hm⟩ := hcof (ULift.up (OrderDual.toDual ⟨L, PrimeSpectrum.zeroLocus_eq_iff.mp hL⟩))
  exact ⟨m, (partialInfIdeal_le _ m).trans hm⟩

/-! ### Stacks 0APW -/

/-- **Stacks 0APW (1).** Let `X = Spec A` be an affine scheme over `S` and `T = V(I)` a closed
subset. If the formal completion `X_{/T}` is countably indexed and `T = V(e 0, e 1, …)` is cut
out by countably many elements of `A`, then `X_{/T}` is adic\*.

By `exists_isCofinalVanishingSequence_of_isCountablyIndexed` the countable indexedness gives a
cofinal sequence `J` of ideals cutting out `T`; by `countableCompletionIsoZeroLocusCompletion`
the completion is the colimit of the `Spec (A ⧸ J n)`, which is adic\* by
`isAdicStar_countableCompletion`. -/
@[stacks 0APW "clause (1)"]
theorem isAdicStar_zeroLocusCompletion_of_isCountablyIndexed (I : Ideal A) (e : ℕ → A)
    (heI : PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (Set.range e))
    (hX : IsCountablyIndexed B S hS (zeroLocusCompletion B S hS hA f I)) :
    IsAdicStar B S hS (zeroLocusCompletion B S hS hA f I) := by
  obtain ⟨J, hJ⟩ := exists_isCofinalVanishingSequence_of_isCountablyIndexed B S hS hA f I hX
  exact isAdicStar_of_iso B S hS (countableCompletionIsoZeroLocusCompletion B S hS hA f I J hJ)
    (isAdicStar_countableCompletion B S hS f hA J hJ e heI)

/-- **Stacks 0APW (2).** The conclusion of clause (1) fails without the countability of the
equations: for Gabber's ring `A` and `T = V(x_α : α ∈ ω₁)`, the formal completion `X_{/T}` of
`X = Spec A` is countably indexed but not adic\*, and so `T` is not cut out by countably many
elements of `A`.

The completion is identified with `gabberCompletionSheaf`, the colimit along the cofinal
sequence `J_n = (x_α^(n+1))`, by `countableCompletionIsoZeroLocusCompletion`, and
`isCountablyIndexed_not_isAdicStar_gabberCompletionSheaf` is the statement for that sheaf. The
last conjunct follows from clause (1). -/
@[stacks 0APW "clause (2)"]
theorem isCountablyIndexed_not_isAdicStar_zeroLocusCompletion_gabber (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (hA : B.Contains (Spec (.of GabberRing.{u})))
    (f : Spec (.of GabberRing.{u}) ⟶ S) :
    IsCountablyIndexed B S hS (zeroLocusCompletion B S hS hA f gabberVanishingIdeal.{u}) ∧
      ¬ IsAdicStar B S hS (zeroLocusCompletion B S hS hA f gabberVanishingIdeal.{u}) ∧
      ¬ ∃ e : ℕ → GabberRing.{u},
        PrimeSpectrum.zeroLocus (gabberVanishingIdeal.{u} : Set GabberRing.{u}) =
          PrimeSpectrum.zeroLocus (Set.range e) := by
  let φ := countableCompletionIsoZeroLocusCompletion B S hS hA f gabberVanishingIdeal.{u}
    gabberPowerIdeal.{u} isCofinalVanishingSequence_gabberPowerIdeal.{u}
  obtain ⟨⟨D, hD, ⟨ψ⟩⟩, hnot⟩ :=
    isCountablyIndexed_not_isAdicStar_gabberCompletionSheaf B S hS f hA
  have hci : IsCountablyIndexed B S hS
      (zeroLocusCompletion B S hS hA f gabberVanishingIdeal.{u}) := ⟨D, hD, ⟨φ.symm ≪≫ ψ⟩⟩
  have hna : ¬ IsAdicStar B S hS
      (zeroLocusCompletion B S hS hA f gabberVanishingIdeal.{u}) := fun h =>
    hnot (isAdicStar_of_iso B S hS φ.symm h)
  exact ⟨hci, hna, fun ⟨e, he⟩ =>
    hna (isAdicStar_zeroLocusCompletion_of_isCountablyIndexed B S hS hA f _ e he hci)⟩

end AlgebraicGeometry.FormalSpace

end
