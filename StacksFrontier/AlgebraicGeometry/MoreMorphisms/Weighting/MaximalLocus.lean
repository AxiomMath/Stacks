module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.Semicontinuity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness over the maximum locus of a positive weighting

Let a separated, locally quasi-finite morphism have finite fibres and carry a positive
weighting. Over the open locus of the target where the weighted fibre sum attains its global
maximum, the morphism is finite.

## Main results

* `AlgebraicGeometry.exists_isFinite_restrict_separableDegreeWeightedFiberSum_maxLocus`: the
  maximum locus is open and the morphism restricted over it is finite.

## Implementation notes

Openness of the maximum locus is lower semicontinuity of the weighted fibre sum. Finiteness is
local on the target for the fpqc topology, so it is enough to produce, through each point of the
maximum locus, an étale neighbourhood over which the base change is finite. Such a neighbourhood
comes from the decomposition of the source into open-and-closed pieces finite over an étale
neighbourhood: on the locus where every distinguished piece keeps its weighted fibre sum and the
total is maximal, the residual piece has empty fibre — otherwise it would contribute a strictly
positive amount and push the total above the maximum — so the base change is covered by finitely
many pairwise disjoint opens each finite over the base, hence finite.

## References

* [Stacks Project, Tag 0F3L](https://stacks.math.columbia.edu/tag/0F3L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

private lemma isFinite_of_finite_disjoint_open_cover
    {ι : Type*} [Finite ι] {Q T : Scheme.{u}} (g : Q ⟶ T)
    (V : ι → Q.Opens)
    (hcover : ∀ x, ∃ i, x ∈ V i)
    (hdisj : Pairwise fun i j ↦ Disjoint (V i : Set Q) (V j))
    (hfinite : ∀ i, IsFinite ((V i).ι ≫ g)) : IsFinite g := by
  classical
  have hcover' : ⨆ i, (V i).ι.opensRange = ⊤ := by
    apply Opens.ext
    ext p
    simpa [Scheme.Opens.opensRange_ι] using hcover p
  have hdisj' : Pairwise fun i j ↦ Disjoint (V i).ι.opensRange (V j).ι.opensRange := by
    intro i j hij
    simpa [Scheme.Opens.opensRange_ι, ← Opens.coe_disjoint] using hdisj hij
  let (i : ι) : IsFinite ((V i).ι ≫ g) := hfinite i
  have hcop : IsFinite (Limits.Sigma.desc fun i ↦ (V i).ι ≫ g) := by infer_instance
  let W : ι → Scheme.{u} := fun i ↦ V i
  let hc := (AlgebraicGeometry.nonempty_isColimit_cofanMk_of
    (fun i ↦ (V i).ι) hcover' hdisj').some
  let e : (∐ W) ≅ Q := IsColimit.coconePointUniqueUpToIso
    (coproductIsCoproduct W) hc
  have he (i : ι) : Limits.Sigma.ι W i ≫ e.hom = (V i).ι := by
    simpa [e] using (coproductIsCoproduct W).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have heq : e.hom ≫ g = Limits.Sigma.desc (fun i ↦ (V i).ι ≫ g) := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, he i, Limits.Sigma.ι_desc]
  rw [← e.inv_hom_id_assoc g, heq]
  infer_instance

private lemma isFinite_restrict_of_finite_disjoint_open_cover_except
    {ι : Type*} [Finite ι] {Q T : Scheme.{u}} (g : Q ⟶ T)
    (V : ι → Q.Opens) (bad : ι)
    (hcover : ∀ x, ∃ i, x ∈ V i)
    (hdisj : Pairwise fun i j ↦ Disjoint (V i : Set Q) (V j))
    (hfinite : ∀ i, i ≠ bad → IsFinite ((V i).ι ≫ g)) (W : T.Opens)
    (hbad : ∀ x : (g ⁻¹ᵁ W).toScheme, (g ⁻¹ᵁ W).ι x ∉ V bad) :
    IsFinite (g ∣_ W) := by
  classical
  let QW := g ⁻¹ᵁ W
  let QWs := QW.toScheme
  let j : QWs ⟶ Q := QW.ι
  let E : ι → QWs.Opens := fun i ↦ j ⁻¹ᵁ V i
  have hcov : ∀ x : QWs, ∃ i, x ∈ E i := fun x ↦ hcover (j x)
  have hpair : Pairwise fun i k ↦ Disjoint (E i : Set QWs) (E k) := fun i k hik ↦
    Set.disjoint_left.mpr fun x hxi hxk ↦ Set.disjoint_left.mp (hdisj hik) hxi hxk
  have hEfinite (i : ι) : IsFinite ((E i).ι ≫ (g ∣_ W)) := by
    by_cases hi : i = bad
    · subst i
      have hempty : E bad = ⊥ := by
        apply Opens.ext
        ext x
        simp only [E, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact hbad x
      rw [hempty]
      have : IsEmpty (⊥ : QWs.Opens).toScheme := by
        show IsEmpty (∅ : Set QWs)
        infer_instance
      infer_instance
    · have hpb := (isPullback_morphismRestrict j (V i)).paste_vert
        (isPullback_morphismRestrict g W).flip
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb (hfinite i hi)
  exact isFinite_of_finite_disjoint_open_cover (g ∣_ W) E hcov hpair hEfinite

private lemma isOpen_eq_of_lowerSemicontinuous_of_le
    {Y : Type*} [TopologicalSpace Y] (s : Y → ℤ) (d : ℤ)
    (hls : LowerSemicontinuous s) (hle : ∀ y, s y ≤ d) :
    IsOpen {y | s y = d} := by
  have heq : {y | s y = d} = s ⁻¹' Set.Ioi (d - 1) := by
    ext y
    have := hle y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro <;> omega
  rw [heq]
  exact lowerSemicontinuous_iff_isOpen_preimage.mp hls (d - 1)

private lemma isFinite_pullback_of_restrict_baseChange
    {X Y B : Scheme.{u}} (f : X ⟶ Y) (j : B ⟶ Y)
    (W : Y.Opens) (V : B.Opens) (hV : V ≤ j ⁻¹ᵁ W)
    (hfinite : IsFinite ((pullback.snd f j) ∣_ V)) :
    IsFinite (pullback.snd (f ∣_ W) (j.resLE W V hV)) := by
  classical
  let P := pullback f j
  let π : P ⟶ B := pullback.snd f j
  let Q := (π ⁻¹ᵁ V).toScheme
  let k : Q ⟶ P := (π ⁻¹ᵁ V).ι
  let πV : Q ⟶ V := π ∣_ V
  let α : Q ⟶ X := k ≫ pullback.fst f j
  let t : (V : B.Opens).toScheme ⟶ (W : Y.Opens).toScheme :=
    Scheme.Hom.resLE j W V hV
  let β : Q ⟶ W := πV ≫ t
  have houter : IsPullback πV α (V.ι ≫ j) f := by
    dsimp [πV, α, π, Q, k, P]
    exact (isPullback_morphismRestrict (pullback.snd f j) V).paste_vert
      (IsPullback.of_hasPullback f j).flip
  have hcomm : α ≫ f = β ≫ W.ι := by
    calc
      α ≫ f = πV ≫ (V.ι ≫ j) := houter.w.symm
      _ = πV ≫ (t ≫ W.ι) := by
        rw [Scheme.Hom.resLE_comp_ι j hV]
      _ = β ≫ W.ι := by simp [β, Category.assoc]
  let l : Q ⟶ pullback f W.ι := pullback.lift α β hcomm
  let a : Q ⟶ (f ⁻¹ᵁ W).toScheme := l ≫ (pullbackRestrictIsoRestrict f W).hom
  have haX : a ≫ (f ⁻¹ᵁ W).ι = α := by
    show (l ≫ (pullbackRestrictIsoRestrict f W).hom) ≫ (f ⁻¹ᵁ W).ι = α
    rw [Category.assoc, pullbackRestrictIsoRestrict_hom_ι, pullback.lift_fst]
  have haF : a ≫ (f ∣_ W) = β := by
    show (l ≫ (pullbackRestrictIsoRestrict f W).hom) ≫ (f ∣_ W) = β
    rw [Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict, pullback.lift_snd]
  have houter' :
      IsPullback πV (a ≫ (f ⁻¹ᵁ W).ι) (t ≫ W.ι) f := by
    rw [haX, Scheme.Hom.resLE_comp_ι j hV]
    exact houter
  have hpull : IsPullback πV a t (f ∣_ W) :=
    IsPullback.of_bot (h₁₁ := πV) (h₂₁ := f ∣_ W) (h₃₁ := f)
      (v₁₁ := a) (v₁₂ := t) (v₂₁ := (f ⁻¹ᵁ W).ι) (v₂₂ := W.ι)
      houter' (by rw [haF]) (isPullback_morphismRestrict f W)
  show IsFinite (pullback.snd (f ∣_ W) t)
  rw [← hpull.flip.isoPullback_inv_snd]
  have : IsFinite πV := hfinite
  infer_instance

/-- Over an étale neighbourhood of a point of the maximum locus there is an open subset
containing the distinguished point, still inside the maximum locus, over which the base change
is finite. -/
private lemma exists_isOpen_isFinite_restrict_of_isGreatest
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsSeparated f]
    (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite) (w : X → ℤ)
    (hw : IsWeighting f w) (hpositive : ∀ x : X, 0 < w x)
    (d : ℤ)
    (hmax : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d)
    {y : Y} (hy : separableDegreeWeightedFiberSum f w y = d)
    (n : ℕ) (xs : Fin n → f.fiber y) (hxs : Function.Surjective xs)
    (U : EtaleNeighborhood Y y)
    (m : Fin n → ℕ) (D : Option (Σ i, Fin (m i)) → (pullback f U.toBase).Opens)
    (hdisj : Set.PairwiseDisjoint Set.univ (fun k ↦ (D k).1))
    (hcover : (⋃ k, (D k).1) = Set.univ)
    (hpieces : ∀ i j, IsFinite ((D (some ⟨i, j⟩)).ι ≫ pullback.snd f U.toBase))
    (hnone : ∀ z : D none,
      ((D none).ι ≫ pullback.snd f U.toBase) z = U.point →
        ∀ i, ((D none).ι ≫ pullback.fst f U.toBase) z ≠ f.fiberι y (xs i)) :
    ∃ T : U.scheme.Opens, U.point ∈ T ∧
      (∀ z ∈ T, separableDegreeWeightedFiberSum f w (U.toBase z) = d) ∧
      IsFinite ((pullback.snd f U.toBase) ∣_ T) := by
  classical
  let P := pullback f U.toBase
  let fst : P ⟶ X := pullback.fst f U.toBase
  let π : P ⟶ U.scheme := pullback.snd f U.toBase
  let wP : P → ℤ := w ∘ fst
  let A := Σ i : Fin n, Fin (m i)
  let part : Option A → U.scheme → ℤ := fun k ↦
    separableDegreeWeightedFiberSum ((D k).ι ≫ π) (wP ∘ (D k).ι)
  have hfiniteP : ∀ u, (π ⁻¹' {u}).Finite := fun u ↦
    finite_preimage_singleton_of_isPullback f fst π U.toBase
      (IsPullback.of_hasPullback f U.toBase) hfinite u
  have hfiniteD : ∀ (k : Option A) (u : U.scheme), (((D k).ι ≫ π) ⁻¹' {u}).Finite := by
    intro k u
    have hpre : ((D k).ι ≫ π) ⁻¹' ({u} : Set U.scheme) =
        (D k).ι ⁻¹' (π ⁻¹' ({u} : Set U.scheme)) := rfl
    rw [hpre]
    exact Set.Finite.preimage (D k).ι.isOpenEmbedding.injective.injOn (hfiniteP u)
  have hdisj' : ∀ i j : Option A, i ≠ j → Disjoint (D i : Set P) (D j : Set P) :=
    fun i j hij ↦ hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hcover' : ∀ p : P, ∃ k, p ∈ D k := by
    intro p
    have hp : p ∈ ⋃ k : Option A, (D k).1 := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hp
  have hsum : ∀ u, separableDegreeWeightedFiberSum π wP u = ∑ k : Option A, part k u := by
    intro u
    have h := congrFun
      (separableDegreeWeightedFiberSum_eq_sum_opens π wP D hdisj' hcover' hfiniteP) u
    simpa only [Finset.sum_apply] using h
  have hbasechange : ∀ u : U.scheme,
      separableDegreeWeightedFiberSum f w (U.toBase u) =
        separableDegreeWeightedFiberSum π wP u := fun u ↦
    congrFun (separableDegreeWeightedFiberSum_comp_of_isPullback
      f fst π U.toBase (IsPullback.of_hasPullback f U.toBase) hfinite w) u
  have huniv : (Finset.univ : Finset (Option A)) = Finset.insertNone Finset.univ := by
    ext k
    cases k <;> simp
  have hcomm : ∀ k : Option A, (D k).ι ≫ fst ≫ f = ((D k).ι ≫ π) ≫ U.toBase := by
    intro k
    have h := congrArg (fun q : P ⟶ Y => (D k).ι ≫ q)
      (pullback.condition (f := f) (g := U.toBase))
    simpa only [Category.assoc] using h
  have hlift : ∀ k : Option A,
      pullback.lift ((D k).ι ≫ fst) ((D k).ι ≫ π) (hcomm k) = (D k).ι := by
    intro k
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  have hpiece_lc : ∀ a : A, IsLocallyConstant (part (some a)) := by
    intro a
    exact hw.isLocallyConstant ((D (some a)).ι ≫ fst) ((D (some a)).ι ≫ π)
      U.toBase (hcomm (some a)) inferInstance
      (by rw [hlift (some a)]; infer_instance) (hpieces a.1 a.2)
  let Tset : Set U.scheme :=
    {u | separableDegreeWeightedFiberSum f w (U.toBase u) = d} ∩
      ⋂ a : A, {u | part (some a) u = part (some a) U.point}
  have hTopen : IsOpen Tset := by
    refine ((isOpen_eq_of_lowerSemicontinuous_of_le _ d
      (lowerSemicontinuous_separableDegreeWeightedFiberSum f hfinite w hw hpositive)
      (fun z ↦ hmax.2 ⟨z, rfl⟩)).preimage U.toBase.continuous).inter ?_
    have : Fintype A := inferInstance
    exact isOpen_iInter_of_finite fun a ↦ (hpiece_lc a).isOpen_fiber _
  let T : U.scheme.Opens := ⟨Tset, hTopen⟩
  have hTpoint : U.point ∈ T := by
    refine ⟨?_, Set.mem_iInter.mpr fun a ↦ rfl⟩
    show separableDegreeWeightedFiberSum f w (U.toBase U.point) = d
    rw [U.map_point]
    exact hy
  have hres_zero : part none U.point = 0 := by
    refine separableDegreeWeightedFiberSum_eq_zero_of_fiber_eq_empty _ _ _ ?_
    exact fiber_eq_empty_of_forall_ne f y xs hxs U (D none) hnone
  have hcenter : separableDegreeWeightedFiberSum f w y = ∑ a : A, part (some a) U.point := by
    calc
      separableDegreeWeightedFiberSum f w y =
          separableDegreeWeightedFiberSum π wP U.point := by
        have hbc := hbasechange U.point
        rwa [U.map_point] at hbc
      _ = ∑ k : Option A, part k U.point := hsum U.point
      _ = part none U.point + ∑ a : A, part (some a) U.point := by
        rw [huniv, Finset.sum_insertNone]
      _ = ∑ a : A, part (some a) U.point := by rw [hres_zero, zero_add]
  have hbad : ∀ x : (π ⁻¹ᵁ T).toScheme, (π ⁻¹ᵁ T).ι x ∉ D none := by
    intro x hx
    let p : P := (π ⁻¹ᵁ T).ι x
    let u : U.scheme := π p
    have hu : u ∈ T := x.2
    have htotal : separableDegreeWeightedFiberSum π wP u = d := by
      rw [← hbasechange u]
      exact hu.1
    have hselected : (∑ a : A, part (some a) u) = d := by
      calc
        (∑ a : A, part (some a) u) = ∑ a : A, part (some a) U.point :=
          Finset.sum_congr rfl fun a _ ↦ (Set.mem_iInter.mp hu.2) a
        _ = separableDegreeWeightedFiberSum f w y := hcenter.symm
        _ = d := hy
    have hdecomp : separableDegreeWeightedFiberSum π wP u =
        part none u + ∑ a : A, part (some a) u := by
      rw [hsum u, huniv, Finset.sum_insertNone]
    have hzero : part none u = 0 := by omega
    have hposPart : 0 < part none u := by
      have : LocallyQuasiFinite ((D none).ι ≫ π) := inferInstance
      exact separableDegreeWeightedFiberSum_pos ((D none).ι ≫ π) (hfiniteD none)
        (wP ∘ (D none).ι) (fun q ↦ hpositive (fst ((D none).ι q))) u ⟨⟨p, hx⟩, rfl⟩
    omega
  have hpiecesfinite : ∀ k : Option A, k ≠ none → IsFinite ((D k).ι ≫ π) := by
    intro k hk
    cases k with
    | none => exact (hk rfl).elim
    | some a => exact hpieces a.1 a.2
  exact ⟨T, hTpoint, fun _ hz ↦ hz.1,
    isFinite_restrict_of_finite_disjoint_open_cover_except
      (ι := Option A) (Q := P) (T := U.scheme) (g := π) (V := D)
      (bad := (none : Option A)) (hcover := hcover') (hdisj := hdisj')
      (hfinite := hpiecesfinite) (W := T) (hbad := hbad)⟩

/-- **Stacks Project, Tag 0F3L.** A separated locally quasi-finite morphism with finite fibres
and a positive weighting is finite over the open locus where its weighted fibre sum attains its
global maximum. -/
@[stacks 0F3L]
theorem exists_isFinite_restrict_separableDegreeWeightedFiberSum_maxLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsSeparated f]
    (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (w : X → ℤ) (hw : IsWeighting f w)
    (hpositive : ∀ x : X, 0 < w x)
    (d : ℤ)
    (hmax : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d) :
    ∃ U : Y.Opens,
      (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d} ∧
        IsFinite (f ∣_ U) := by
  classical
  let U : Y.Opens := ⟨_, isOpen_eq_of_lowerSemicontinuous_of_le _ d
    (lowerSemicontinuous_separableDegreeWeightedFiberSum f hfinite w hw hpositive)
    (fun y ↦ hmax.2 ⟨y, rfl⟩)⟩
  refine ⟨U, rfl, ?_⟩
  have hlocal (y : U) : ∃ (B : Scheme.{u}) (j : B ⟶ U),
      Etale j ∧ (∃ b, j b = y) ∧ IsFinite (pullback.snd (f ∣_ U) j) := by
    obtain ⟨n, xs, hxs, hxi⟩ := exists_fin_bijective_isolated_fiber f hfinite y.1
    obtain ⟨N, m, D, v, hdisj, hcover, _hclopen, hpieces, hnone⟩ :=
      exists_etaleNeighborhood_purelyInseparable_decomposition f n y.1 xs hxs.1 hxi
    obtain ⟨T, ht, hTmax, hTfin⟩ := exists_isOpen_isFinite_restrict_of_isGreatest
      f hfinite w hw hpositive d hmax y.2 n xs hxs.2
        N m D hdisj hcover (fun i j ↦ (hpieces i j).1) hnone
    have hTU : T ≤ N.toBase ⁻¹ᵁ U := fun z hz ↦ hTmax z hz
    refine ⟨T, N.toBase.resLE U T hTU, inferInstance, ?_,
      isFinite_pullback_of_restrict_baseChange f N.toBase U T hTU hTfin⟩
    refine ⟨⟨N.point, ht⟩, ?_⟩
    apply Subtype.ext
    have heq := congrArg (fun k : T.toScheme ⟶ Y ↦ k ⟨N.point, ht⟩)
      (Scheme.Hom.resLE_comp_ι N.toBase hTU)
    exact heq.trans N.map_point
  choose B j hj hpoint hfin using hlocal
  let C : U.toScheme.Cover Scheme.fppfPrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) U B j
      (fun y ↦ ⟨y, hpoint y⟩) (fun y ↦ by
        let := hj y
        exact ⟨inferInstance, inferInstance⟩)
  have : MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
    Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc_of_isAffineHom inferInstance
  exact MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := @IsFinite) (K := Scheme.fpqcPrecoverage)
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ C.mem₀)
    (by rintro _ _ _ ⟨y⟩; exact hfin y)

end AlgebraicGeometry
