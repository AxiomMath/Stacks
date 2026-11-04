module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FiniteChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.PurelyInseparablePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of weightings

The pullback of a weighting of a locally quasi-finite morphism along an arbitrary base change is
again a weighting.

## Main results

* `AlgebraicGeometry.IsWeighting.comp_of_isPullback`: a weighting pulls back to a weighting along
  an arbitrary base change.

## Implementation notes

The base-change diagram is expressed by `CategoryTheory.IsPullback`, so the result applies to any
object realizing the fibre product and not only to a chosen pullback construction. Local
quasi-finiteness is `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.LocallyQuasiFinite`.

Checking the weighting condition for the base change amounts to checking that the weighted fibre
sum of a finite open chart of the base change is locally constant. The source is decomposed, over
a further étale neighbourhood, into open-and-closed pieces which are finite over the
neighbourhood and meet the distinguished fibre in a single point with purely inseparable
residue-field extension. Each such piece agrees, after shrinking the base, with a piece of a
chart of the original morphism, because two finite open immersions into a common scheme with the
same single point over the base agree on a neighbourhood of that point; the weighting hypothesis
then makes each piece contribute a locally constant function, and the residual piece contributes
zero.

## References

* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Filter
open scoped Topology

/-- Through any point of the source of a locally quasi-finite morphism locally of finite type
there is a single finite open chart over an étale neighbourhood of its image which meets the
distinguished fibre in one point above the given point, with purely inseparable residue-field
extension. -/
private theorem exists_finite_open_chart_at_point
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (x : X) :
    ∃ (N : EtaleNeighborhood Y (f x))
      (D : (pullback f N.toBase).Opens) (a : D),
      let π := D.ι ≫ pullback.snd f N.toBase
      let h := D.ι ≫ pullback.fst f N.toBase
      IsFinite π ∧ π ⁻¹' {N.point} = {a} ∧ h a = x ∧
        ∃ ha : π a = N.point,
          ((N.scheme.residueFieldCongr ha).inv ≫
            π.residueFieldMap a).hom.IsPurelyInseparable := by
  obtain ⟨N, m, D, a, hspec, hcover⟩ := exists_finite_opens_chart_at_point f x
  obtain ⟨z, hzX, hzN⟩ :=
    Scheme.Pullback.exists_preimage_pullback x N.point N.map_point.symm
  obtain ⟨j, hj⟩ := hcover z hzN hzX
  exact ⟨N, D j, a j, hspec j⟩

private theorem eventually_eq_of_etale_neighborhood
    {V : Scheme.{u}} (F : V → ℤ) (v : V)
    (h : ∃ (T : Scheme.{u}) (q : T ⟶ V) (t : T),
      Etale q ∧ q t = v ∧ IsLocallyConstant (F ∘ q)) :
    ∀ᶠ v' in 𝓝 v, F v' = F v := by
  obtain ⟨T, q, t, hq, hqt, hF⟩ := h
  have : Etale q := hq
  obtain ⟨N, hN, htN, hconst⟩ :=
    exists_open_neighborhood_eq_of_isLocallyConstant_comp_of_isOpenMap
      q q.isOpenMap F hF t
  filter_upwards [hN.mem_nhds (hqt ▸ htN)] with v' hv'
  simpa only [hqt] using hconst v' hv'

private theorem eventually_eq_finset_sum
    {ι V : Type*} [TopologicalSpace V]
    (s : Finset ι) (F : ι → V → ℤ) (v : V)
    (h : ∀ i ∈ s, ∀ᶠ v' in 𝓝 v, F i v' = F i v) :
    ∀ᶠ v' in 𝓝 v, (∑ i ∈ s, F i v') = ∑ i ∈ s, F i v := by
  filter_upwards [(Filter.eventually_all_finset s).2 h] with v' hv' using Finset.sum_congr rfl hv'

/-- The points of a finite `A` over `S` mapping outside the range of an open immersion `j` have
closed image in `S`, which misses `s` when the only point over `s` maps into the range of `j`. -/
private theorem exists_isClosed_image_not_mem_range
    {A B C S : Scheme.{u}} (f : A ⟶ S) (k : C ⟶ S) (i : A ⟶ C) (j : B ⟶ C)
    [IsFinite f] [IsOpenImmersion j] (hi : i ≫ k = f)
    (s : S) (a : A) (hja : i a ∈ Set.range j) (hfa_unique : ∀ a', f a' = s → a' = a) :
    ∃ T : Set S, IsClosed T ∧ s ∉ T ∧ ∀ c, c ∈ Set.range i → c ∉ Set.range j → k c ∈ T := by
  refine ⟨f '' (i ⁻¹' (Set.range j)ᶜ),
    f.isClosedMap _ (j.isOpenEmbedding.isOpen_range.isClosed_compl.preimage i.continuous), ?_, ?_⟩
  · rintro ⟨a', ha', hfa'⟩
    rw [hfa_unique a' hfa'] at ha'
    exact ha' hja
  · rintro c ⟨a', rfl⟩ h
    exact ⟨a', h, by rw [← hi, Scheme.Hom.comp_apply]⟩

private theorem open_immersion_ranges_agree_after_finite_shrinking
    {A B C S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S) (k : C ⟶ S)
    (i : A ⟶ C) (j : B ⟶ C) [IsFinite f] [IsFinite g]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hi : i ≫ k = f) (hj : j ≫ k = g)
    (s : S) (a : A) (b : B) (hab : i a = j b)
    (hfa_unique : ∀ a', f a' = s → a' = a)
    (hgb_unique : ∀ b', g b' = s → b' = b) :
    ∃ W : Set S, IsOpen W ∧ s ∈ W ∧
      ∀ c, k c ∈ W → (c ∈ Set.range i ↔ c ∈ Set.range j) := by
  obtain ⟨T₁, hT₁, hs₁, h₁⟩ := exists_isClosed_image_not_mem_range f k i j hi s a
    ⟨b, hab.symm⟩ hfa_unique
  obtain ⟨T₂, hT₂, hs₂, h₂⟩ := exists_isClosed_image_not_mem_range g k j i hj s b
    ⟨a, hab⟩ hgb_unique
  exact ⟨(T₁ ∪ T₂)ᶜ, (hT₁.union hT₂).isOpen_compl, by simp [hs₁, hs₂], fun c hc ↦
    ⟨fun hci ↦ by_contra fun h ↦ hc (.inl (h₁ c hci h)),
      fun hcj ↦ by_contra fun h ↦ hc (.inr (h₂ c hcj h))⟩⟩

/-- The range of the restriction of an open immersion `i` over `k ⁻¹ᵁ W` is the preimage of the
range of `i`. -/
private theorem range_resLE_eq_preimage_range
    {A C S : Scheme.{u}} (f : A ⟶ S) (k : C ⟶ S) (i : A ⟶ C) [IsOpenImmersion i]
    (hi : i ≫ k = f) (W : S.Opens) (hle : f ⁻¹ᵁ W ≤ i ⁻¹ᵁ (k ⁻¹ᵁ W)) :
    Set.range (i.resLE (k ⁻¹ᵁ W) (f ⁻¹ᵁ W) hle) = (k ⁻¹ᵁ W).ι ⁻¹' Set.range i := by
  have hmap (x : (f ⁻¹ᵁ W).toScheme) :
      (k ⁻¹ᵁ W).ι (i.resLE (k ⁻¹ᵁ W) (f ⁻¹ᵁ W) hle x) = i ((f ⁻¹ᵁ W).ι x) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : (f ⁻¹ᵁ W).toScheme ⟶ C ↦ m x) (Scheme.Hom.resLE_comp_ι i hle)
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (hmap x).symm⟩
  · rintro ⟨x, hx⟩
    have hxW : f x ∈ W := by
      rw [← hi, Scheme.Hom.comp_apply, hx]
      exact c.2
    exact ⟨⟨x, hxW⟩, Subtype.ext ((hmap _).trans hx)⟩

private theorem exists_iso_of_finite_open_immersions_agree_near_fiber
    {A B C S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S) (k : C ⟶ S)
    (i : A ⟶ C) (j : B ⟶ C) [IsFinite f] [IsFinite g]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hi : i ≫ k = f) (hj : j ≫ k = g)
    (s : S) (a : A) (b : B) (hab : i a = j b)
    (hfa_unique : ∀ a', f a' = s → a' = a)
    (hgb_unique : ∀ b', g b' = s → b' = b) :
    ∃ W : S.Opens, s ∈ W ∧
      ∃ e : (f ⁻¹ᵁ W).toScheme ≅ (g ⁻¹ᵁ W).toScheme,
        e.hom ≫ g.resLE W (g ⁻¹ᵁ W) le_rfl =
          f.resLE W (f ⁻¹ᵁ W) le_rfl ∧
        e.hom ≫ (g ⁻¹ᵁ W).ι ≫ j = (f ⁻¹ᵁ W).ι ≫ i := by
  obtain ⟨Wset, hWset, hsW, hrange⟩ :=
    open_immersion_ranges_agree_after_finite_shrinking
      f g k i j hi hj s a b hab hfa_unique hgb_unique
  let W : S.Opens := ⟨Wset, hWset⟩
  let A₀ := f ⁻¹ᵁ W
  let B₀ := g ⁻¹ᵁ W
  let C₀ := k ⁻¹ᵁ W
  have hle {P : Scheme.{u}} (m : P ⟶ S) (n : P ⟶ C) (h : n ≫ k = m) :
      m ⁻¹ᵁ W ≤ n ⁻¹ᵁ C₀ := by
    rw [← Scheme.Hom.comp_preimage, h]
  let i₀ : A₀.toScheme ⟶ C₀.toScheme := i.resLE C₀ A₀ (hle f i hi)
  let j₀ : B₀.toScheme ⟶ C₀.toScheme := j.resLE C₀ B₀ (hle g j hj)
  have hi₀' : i₀ ≫ C₀.ι = A₀.ι ≫ i := Scheme.Hom.resLE_comp_ι i _
  have hj₀' : j₀ ≫ C₀.ι = B₀.ι ≫ j := Scheme.Hom.resLE_comp_ι j _
  have hrange₀ : Set.range i₀ = Set.range j₀ := by
    rw [range_resLE_eq_preimage_range f k i hi W, range_resLE_eq_preimage_range g k j hj W]
    ext c
    exact hrange (C₀.ι c) c.2
  have : IsOpenImmersion i₀ := by
    dsimp [i₀, Scheme.Hom.resLE]
    infer_instance
  have : IsOpenImmersion j₀ := by
    dsimp [j₀, Scheme.Hom.resLE]
    infer_instance
  let e := IsOpenImmersion.isoOfRangeEq i₀ j₀ hrange₀
  have hfac : e.hom ≫ j₀ = i₀ := IsOpenImmersion.isoOfRangeEq_hom_fac ..
  have hmiddle : e.hom ≫ B₀.ι ≫ g = A₀.ι ≫ f := by
    rw [← hj, ← hi, ← reassoc_of% hj₀', ← reassoc_of% hi₀', reassoc_of% hfac]
  refine ⟨W, hsW, e, ?_, ?_⟩
  · apply (cancel_mono W.ι).1
    rwa [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
  · calc
      e.hom ≫ B₀.ι ≫ j = e.hom ≫ j₀ ≫ C₀.ι := by
        rw [hj₀']
      _ = i₀ ≫ C₀.ι := by simp only [← Category.assoc, hfac]
      _ = A₀.ι ≫ i := hi₀'

private theorem separableDegreeWeightedFiberSum_eq_of_iso
    {A B S : Scheme.{u}} (e : A ≅ B) (fA : A ⟶ S) (fB : B ⟶ S)
    (comm : e.hom ≫ fB = fA) [LocallyQuasiFinite fB]
    (hfinite : ∀ s, (fB ⁻¹' {s}).Finite) (wA : A → ℤ) (wB : B → ℤ)
    (hw : wA = wB ∘ e.hom) :
    separableDegreeWeightedFiberSum fA wA =
      separableDegreeWeightedFiberSum fB wB := by
  have hsquare : IsPullback e.hom fA fB (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨comm⟩
  have hbc := separableDegreeWeightedFiberSum_comp_of_isPullback
    fB e.hom fA (𝟙 S) hsquare hfinite wB
  simpa [Function.comp_def, hw] using hbc.symm

private theorem locallyConstant_weightedFiberSum_after_baseChange
    {U V U' V' : Scheme.{u}} (π : U ⟶ V) (q : V' ⟶ V) (π' : U' ⟶ V')
    (h : U' ⟶ U) (sq : IsPullback h π' π q) (w : U → ℤ)
    [LocallyQuasiFinite π] (hfinite : ∀ v, (π ⁻¹' {v}).Finite)
    (hLC : IsLocallyConstant
      (separableDegreeWeightedFiberSum π w)) :
    IsLocallyConstant
      (separableDegreeWeightedFiberSum π' (w ∘ h)) := by
  rw [← separableDegreeWeightedFiberSum_comp_of_isPullback
    π h π' q sq hfinite w]
  exact hLC.comp_continuous q.continuous

private theorem locallyConstant_weightedFiberSum_of_iso_on_open
    {A B S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S) [IsFinite f] [IsFinite g]
    (W : S.Opens)
    (e : (f ⁻¹ᵁ W).toScheme ≅ (g ⁻¹ᵁ W).toScheme)
    (he : e.hom ≫ g.resLE W (g ⁻¹ᵁ W) le_rfl = f.resLE W (f ⁻¹ᵁ W) le_rfl)
    (wA : A → ℤ) (wB : B → ℤ)
    (hLC : IsLocallyConstant (separableDegreeWeightedFiberSum g wB))
    (hweight : wA ∘ (f ⁻¹ᵁ W).ι = wB ∘ (g ⁻¹ᵁ W).ι ∘ e.hom) :
    IsLocallyConstant
      (separableDegreeWeightedFiberSum
        (f.resLE W (f ⁻¹ᵁ W) le_rfl) (wA ∘ (f ⁻¹ᵁ W).ι)) := by
  classical
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at he ⊢
  have hLCg := locallyConstant_weightedFiberSum_after_baseChange
    g W.ι (g ∣_ W) (g ⁻¹ᵁ W).ι
    (isPullback_morphismRestrict g W).flip wB g.finite_preimage_singleton hLC
  have hEq := separableDegreeWeightedFiberSum_eq_of_iso e
    (f ∣_ W) (g ∣_ W) he
    (fun t => (g ∣_ W).finite_preimage_singleton t)
    (wA ∘ (f ⁻¹ᵁ W).ι) (wB ∘ (g ⁻¹ᵁ W).ι) hweight
  exact hEq.symm ▸ hLCg

private theorem locallyConstant_weightedFiberSum_near_matching_finite_opens
    {A B C S : Scheme.{u}} (fA : A ⟶ S) (fB : B ⟶ S) (k : C ⟶ S)
    (i : A ⟶ C) (j : B ⟶ C) [IsFinite fA] [IsFinite fB]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hi : i ≫ k = fA) (hj : j ≫ k = fB)
    (s : S) (a : A) (b : B) (hab : i a = j b)
    (hfa_unique : ∀ a', fA a' = s → a' = a)
    (hfb_unique : ∀ b', fB b' = s → b' = b)
    (w : C → ℤ)
    (hLCB : IsLocallyConstant
      (separableDegreeWeightedFiberSum fB (w ∘ j))) :
    ∃ W : S.Opens, s ∈ W ∧
      IsLocallyConstant
        (separableDegreeWeightedFiberSum fA (w ∘ i) ∘ W.ι) := by
  obtain ⟨W, hsW, e, heS, heC⟩ :=
    exists_iso_of_finite_open_immersions_agree_near_fiber
      fA fB k i j hi hj s a b hab hfa_unique hfb_unique
  have hweight : (w ∘ i) ∘ (fA ⁻¹ᵁ W).ι =
      (w ∘ j) ∘ (fB ⁻¹ᵁ W).ι ∘ e.hom := by
    funext x
    exact congrArg w (congrArg (fun m : (fA ⁻¹ᵁ W).toScheme ⟶ C ↦ m x) heC).symm
  have hLCres := locallyConstant_weightedFiberSum_of_iso_on_open
    fA fB W e heS (w ∘ i) (w ∘ j) hLCB hweight
  have hfinite : ∀ t, (fA ⁻¹' {t}).Finite := fun t ↦ fA.finite_preimage_singleton t
  have hbase := separableDegreeWeightedFiberSum_comp_of_isPullback
    fA (fA ⁻¹ᵁ W).ι (fA ∣_ W) W.ι
    (isPullback_morphismRestrict fA W).flip hfinite (w ∘ i)
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hLCres
  refine ⟨W, hsW, ?_⟩
  rwa [hbase]
private noncomputable def compatibilityBaseMap
    {X Y A B N V : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (hA : A ⟶ X) (πA : A ⟶ N) (commA : hA ≫ f = πA ≫ gN)
    (hB : B ⟶ X) (πB : B ⟶ V) (commB : hB ≫ f = πB ≫ gV) :
    pullback hA hB ⟶ pullback gN gV :=
  pullback.lift (pullback.fst hA hB ≫ πA) (pullback.snd hA hB ≫ πB) (by
    simp only [Category.assoc, ← commA, ← commB, pullback.condition_assoc])

private theorem compatibilityBaseMap_fst
    {X Y A B N V : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (hA : A ⟶ X) (πA : A ⟶ N) (commA : hA ≫ f = πA ≫ gN)
    (hB : B ⟶ X) (πB : B ⟶ V) (commB : hB ≫ f = πB ≫ gV) :
    compatibilityBaseMap f gN gV hA πA commA hB πB commB ≫
      pullback.fst gN gV = pullback.fst hA hB ≫ πA := by
  unfold compatibilityBaseMap
  exact pullback.lift_fst _ _ _

private theorem compatibilityBaseMap_snd
    {X Y A B N V : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (hA : A ⟶ X) (πA : A ⟶ N) (commA : hA ≫ f = πA ≫ gN)
    (hB : B ⟶ X) (πB : B ⟶ V) (commB : hB ≫ f = πB ≫ gV) :
    compatibilityBaseMap f gN gV hA πA commA hB πB commB ≫
      pullback.snd gN gV = pullback.snd hA hB ≫ πB := by
  unfold compatibilityBaseMap
  exact pullback.lift_snd _ _ _

private noncomputable def compatibleLeftChartMap
    {X Y A B N V : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (hA : A ⟶ X) (πA : A ⟶ N) (commA : hA ≫ f = πA ≫ gN)
    (hB : B ⟶ X) (πB : B ⟶ V) (commB : hB ≫ f = πB ≫ gV) :
    pullback hA hB ⟶ pullback πA (pullback.fst gN gV) :=
  pullback.lift (pullback.fst hA hB)
    (compatibilityBaseMap f gN gV hA πA commA hB πB commB)
    (compatibilityBaseMap_fst f gN gV hA πA commA hB πB commB).symm

private noncomputable def compatibleRightChartMap
    {X Y A B N V : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (hA : A ⟶ X) (πA : A ⟶ N) (commA : hA ≫ f = πA ≫ gN)
    (hB : B ⟶ X) (πB : B ⟶ V) (commB : hB ≫ f = πB ≫ gV) :
    pullback hA hB ⟶ pullback πB (pullback.snd gN gV) :=
  pullback.lift (pullback.snd hA hB)
    (compatibilityBaseMap f gN gV hA πA commA hB πB commB)
    (compatibilityBaseMap_snd f gN gV hA πA commA hB πB commB).symm

private theorem compatibleChartMaps_commute
    {X Y A B N V : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (hA : A ⟶ X) (πA : A ⟶ N) (commA : hA ≫ f = πA ≫ gN)
    (hB : B ⟶ X) (πB : B ⟶ V) (commB : hB ≫ f = πB ≫ gV) :
    compatibleLeftChartMap f gN gV hA πA commA hB πB commB ≫
      baseChangedChartMap f gN (pullback.fst gN gV) hA πA commA ≫
      (pullback.congrHom rfl (pullback.condition (f := gN) (g := gV))).hom =
    compatibleRightChartMap f gN gV hA πA commA hB πB commB ≫
      baseChangedChartMap f gV (pullback.snd gN gV) hB πB commB := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
      pullback.lift_fst, Category.comp_id]
    simp only [baseChangedChartMap_fst]
    simp only [compatibleLeftChartMap, compatibleRightChartMap,
      ← Category.assoc, pullback.lift_fst, pullback.condition]
  · simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
      pullback.lift_snd, Category.comp_id]
    rw [← Category.assoc, baseChangedChartMap_snd]
    simp only [Category.assoc, baseChangedChartMap_snd,
      compatibleLeftChartMap, compatibleRightChartMap,
      pullback.lift_snd]

private noncomputable def baseChangedChartMapToCommon
    {X Y U N V S : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (qN : S ⟶ N) (qV : S ⟶ V) (eqBase : qN ≫ gN = qV ≫ gV)
    (h : U ⟶ X) (π : U ⟶ N) (comm : h ≫ f = π ≫ gN) :
    pullback π qN ⟶ pullback f (qV ≫ gV) :=
  baseChangedChartMap f gN qN h π comm ≫ (pullback.congrHom rfl eqBase).hom

private theorem baseChangedChartMapToCommon_isOpenImmersion
    {X Y U N V S : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (qN : S ⟶ N) (qV : S ⟶ V) (eqBase : qN ≫ gN = qV ≫ gV)
    (h : U ⟶ X) (π : U ⟶ N) (comm : h ≫ f = π ≫ gN)
    [IsOpenImmersion (pullback.lift h π comm)] :
    IsOpenImmersion (baseChangedChartMapToCommon f gN gV qN qV eqBase h π comm) := by
  unfold baseChangedChartMapToCommon
  have := baseChangedChartMap_isOpenImmersion f gN qN h π comm
  infer_instance

private theorem baseChangedChartMapToCommon_fst
    {X Y U N V S : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (qN : S ⟶ N) (qV : S ⟶ V) (eqBase : qN ≫ gN = qV ≫ gV)
    (h : U ⟶ X) (π : U ⟶ N) (comm : h ≫ f = π ≫ gN) :
    baseChangedChartMapToCommon f gN gV qN qV eqBase h π comm ≫
      pullback.fst f (qV ≫ gV) = pullback.fst π qN ≫ h := by
  unfold baseChangedChartMapToCommon
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, baseChangedChartMap_fst]

private theorem baseChangedChartMapToCommon_snd
    {X Y U N V S : Scheme.{u}} (f : X ⟶ Y)
    (gN : N ⟶ Y) (gV : V ⟶ Y)
    (qN : S ⟶ N) (qV : S ⟶ V) (eqBase : qN ≫ gN = qV ≫ gV)
    (h : U ⟶ X) (π : U ⟶ N) (comm : h ≫ f = π ≫ gN) :
    baseChangedChartMapToCommon f gN gV qN qV eqBase h π comm ≫
      pullback.snd f (qV ≫ gV) = pullback.snd π qN := by
  unfold baseChangedChartMapToCommon
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd, Category.comp_id, baseChangedChartMap_snd]
private theorem locallyConstant_weightedFiberSum_after_singleton_chart_baseChange
    {X Y A B N V : Scheme.{u}} (f : X ⟶ Y) (gN : N ⟶ Y) (gV : V ⟶ Y)
    (hA : A ⟶ X) (πA : A ⟶ N) (commA : hA ≫ f = πA ≫ gN)
    (hB : B ⟶ X) (πB : B ⟶ V) (commB : hB ≫ f = πB ≫ gV)
    [Etale gN] [IsFinite πA] [IsFinite πB]
    [IsOpenImmersion (pullback.lift hA πA commA)]
    [IsOpenImmersion (pullback.lift hB πB commB)]
    (w : X → ℤ) (hw : IsWeighting f w)
    (a : A) (b : B) (hab : hA a = hB b)
    (n : N) (hn : πA a = n) (v : V) (hv : πB b = v)
    (hfibA : πA ⁻¹' {n} = {a}) (hfibB : πB ⁻¹' {v} = {b})
    (hpureA : (((N.residueFieldCongr hn).inv ≫ πA.residueFieldMap a).hom).IsPurelyInseparable)
    (hpureB : (((V.residueFieldCongr hv).inv ≫ πB.residueFieldMap b).hom).IsPurelyInseparable) :
    ∃ (T : Scheme.{u}) (q : T ⟶ V) (t : T),
      Etale q ∧ q t = v ∧
      IsLocallyConstant (separableDegreeWeightedFiberSum πB (w ∘ hB) ∘ q) := by
  let S := pullback gN gV
  let qN : S ⟶ N := pullback.fst gN gV
  let qV : S ⟶ V := pullback.snd gN gV
  have heq : qN ≫ gN = qV ≫ gV := pullback.condition
  let C := pullback f (qV ≫ gV)
  let A' := pullback πA qN
  let B' := pullback πB qV
  let fA : A' ⟶ S := pullback.snd πA qN
  let fB : B' ⟶ S := pullback.snd πB qV
  let iA : A' ⟶ C := baseChangedChartMapToCommon f gN gV qN qV heq hA πA commA
  let iB : B' ⟶ C := baseChangedChartMap f gV qV hB πB commB
  have : IsFinite fA := by dsimp [fA]; infer_instance
  have : IsFinite fB := by dsimp [fB]; infer_instance
  have : IsOpenImmersion iA :=
    baseChangedChartMapToCommon_isOpenImmersion f gN gV qN qV heq hA πA commA
  have : IsOpenImmersion iB := baseChangedChartMap_isOpenImmersion f gV qV hB πB commB
  have hiA : iA ≫ pullback.snd f (qV ≫ gV) = fA :=
    baseChangedChartMapToCommon_snd f gN gV qN qV heq hA πA commA
  have hiB : iB ≫ pullback.snd f (qV ≫ gV) = fB :=
    baseChangedChartMap_snd f gV qV hB πB commB
  obtain ⟨r, hra, hrb⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  let m : pullback hA hB ⟶ S :=
    compatibilityBaseMap f gN gV hA πA commA hB πB commB
  let s : S := m r
  let l : pullback hA hB ⟶ A' :=
    compatibleLeftChartMap f gN gV hA πA commA hB πB commB
  let rmap : pullback hA hB ⟶ B' :=
    compatibleRightChartMap f gN gV hA πA commA hB πB commB
  let a' : A' := l r
  let b' : B' := rmap r
  have hqN : qN s = n := by
    simpa only [Scheme.Hom.comp_apply, hra, hn] using
      congrArg (fun t : pullback hA hB ⟶ N ↦ t r)
        (compatibilityBaseMap_fst f gN gV hA πA commA hB πB commB)
  have hqV : qV s = v := by
    simpa only [Scheme.Hom.comp_apply, hrb, hv] using
      congrArg (fun t : pullback hA hB ⟶ V ↦ t r)
        (compatibilityBaseMap_snd f gN gV hA πA commA hB πB commB)
  have haS : fA a' = s := congrArg (fun t : pullback hA hB ⟶ S ↦ t r)
    (pullback.lift_snd (pullback.fst hA hB) m
      (compatibilityBaseMap_fst f gN gV hA πA commA hB πB commB).symm)
  have hbS : fB b' = s := congrArg (fun t : pullback hA hB ⟶ S ↦ t r)
    (pullback.lift_snd (pullback.snd hA hB) m
      (compatibilityBaseMap_snd f gN gV hA πA commA hB πB commB).symm)
  have hAu : ∀ z : A', fA z = s → z = a' := fun z hz ↦
    Scheme.Pullback.eq_of_snd_eq_of_isPurelyInseparable
      πA a n hn hfibA hpureA qN s hqN hz haS
  have hBu : ∀ z : B', fB z = s → z = b' := fun z hz ↦
    Scheme.Pullback.eq_of_snd_eq_of_isPurelyInseparable
      πB b v hv hfibB hpureB qV s hqV hz hbS
  have hab' : iB b' = iA a' := by
    have hm := compatibleChartMaps_commute f gN gV hA πA commA hB πB commB
    have hm' := congrArg (fun t : pullback hA hB ⟶ C ↦ t r) hm
    dsimp only [iA, iB, a', b', baseChangedChartMapToCommon]
    simpa only [Scheme.Hom.comp_apply] using hm'.symm
  let wC : C → ℤ := w ∘ pullback.fst f (qV ≫ gV)
  have hwtA : wC ∘ iA = (w ∘ hA) ∘ pullback.fst πA qN := funext fun z ↦ congrArg w
    (congrArg (fun t : A' ⟶ X ↦ t z)
      (baseChangedChartMapToCommon_fst f gN gV qN qV heq hA πA commA))
  have hwtB : wC ∘ iB = (w ∘ hB) ∘ pullback.fst πB qV := funext fun z ↦ congrArg w
    (congrArg (fun t : B' ⟶ X ↦ t z) (baseChangedChartMap_fst f gV qV hB πB commB))
  have hLC_A : IsLocallyConstant
      (separableDegreeWeightedFiberSum fA (wC ∘ iA)) := by
    rw [hwtA]
    exact locallyConstant_weightedFiberSum_after_baseChange
      πA qN fA (pullback.fst πA qN) (IsPullback.of_hasPullback πA qN)
      (w ∘ hA) (fun t ↦ πA.finite_preimage_singleton t)
      (hw.isLocallyConstant hA πA gN commA inferInstance inferInstance inferInstance)
  obtain ⟨W, hsW, hLC_B⟩ := locallyConstant_weightedFiberSum_near_matching_finite_opens
    fB fA (pullback.snd f (qV ≫ gV)) iB iA hiB hiA
    s b' a' hab' hBu hAu wC hLC_A
  have hBC := separableDegreeWeightedFiberSum_comp_of_isPullback
    πB (pullback.fst πB qV) fB qV (IsPullback.of_hasPullback πB qV)
    (fun t ↦ πB.finite_preimage_singleton t) (w ∘ hB)
  rw [← hwtB] at hBC
  let q : W.toScheme ⟶ V := W.ι ≫ qV
  let t : W.toScheme := ⟨s, hsW⟩
  have : Etale qV := inferInstance
  have : Etale q := by dsimp [q]; infer_instance
  refine ⟨W.toScheme, q, t, inferInstance, hqV, ?_⟩
  show IsLocallyConstant ((separableDegreeWeightedFiberSum πB (w ∘ hB) ∘ qV) ∘ W.ι)
  rwa [hBC]

private theorem eventually_eq_weightedFiberSum_of_singleton_open_piece
    {X Y U V E : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y)
    (comm : h ≫ f = π ≫ g)
    [IsOpenImmersion (pullback.lift h π comm)]
    (q : E ⟶ V) (D : (pullback π q).Opens) (d : D)
    (v : E) (hv : (D.ι ≫ pullback.snd π q) d = v)
    [IsFinite (D.ι ≫ pullback.snd π q)]
    (hfiber : ((D.ι ≫ pullback.snd π q) ⁻¹' {v}) = {d})
    (hpure : (((E.residueFieldCongr hv).inv ≫
      (D.ι ≫ pullback.snd π q).residueFieldMap d).hom).IsPurelyInseparable)
    (w : X → ℤ) (hw : IsWeighting f w) :
    ∀ᶠ t in 𝓝 v,
      separableDegreeWeightedFiberSum
        (D.ι ≫ pullback.snd π q) (w ∘ h ∘ pullback.fst π q ∘ D.ι) t =
      separableDegreeWeightedFiberSum
        (D.ι ≫ pullback.snd π q) (w ∘ h ∘ pullback.fst π q ∘ D.ι) v := by
  let hB : D.toScheme ⟶ X := D.ι ≫ pullback.fst π q ≫ h
  let πB : D.toScheme ⟶ E := D.ι ≫ pullback.snd π q
  let gB : E ⟶ Y := q ≫ g
  have commB : hB ≫ f = πB ≫ gB := by
    dsimp [hB, πB, gB]
    simp only [Category.assoc, comm, pullback.condition_assoc]
  have hLiftB : pullback.lift hB πB commB =
      D.ι ≫ baseChangedChartMap f g q h π comm :=
    pullback.hom_ext ((pullback.lift_fst _ _ _).trans (by simp [hB, gB, baseChangedChartMap_fst]))
      ((pullback.lift_snd _ _ _).trans (by simp [πB, gB, baseChangedChartMap_snd]))
  have : IsOpenImmersion (pullback.lift hB πB commB) := by
    rw [hLiftB]
    have := baseChangedChartMap_isOpenImmersion f g q h π comm
    infer_instance
  let x : X := hB d
  obtain ⟨N, Dsrc, a, hfiniteA, hfiberA, hax, hresA⟩ :=
    exists_finite_open_chart_at_point f x
  let hA : Dsrc.toScheme ⟶ X := Dsrc.ι ≫ pullback.fst f N.toBase
  let πA : Dsrc.toScheme ⟶ N.scheme := Dsrc.ι ≫ pullback.snd f N.toBase
  have commA : hA ≫ f = πA ≫ N.toBase := by
    dsimp [hA, πA]
    simp only [Category.assoc, pullback.condition]
  have hLiftA : pullback.lift hA πA commA = Dsrc.ι := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, hA]
    · simp only [pullback.lift_snd, πA]
  have : IsOpenImmersion (pullback.lift hA πA commA) := by
    rw [hLiftA]
    infer_instance
  have : IsFinite πA := hfiniteA
  obtain ⟨ha, hpureA⟩ := hresA
  have hchart := locallyConstant_weightedFiberSum_after_singleton_chart_baseChange
    f N.toBase gB hA πA commA hB πB commB w hw a d hax
    N.point ha v hv hfiberA hfiber hpureA hpure
  have hev := eventually_eq_of_etale_neighborhood
    (separableDegreeWeightedFiberSum πB (w ∘ hB)) v hchart
  have hweight : w ∘ hB = w ∘ h ∘ pullback.fst π q ∘ D.ι := by
    funext z
    simp only [Function.comp_apply, hB, Scheme.Hom.comp_apply]
  rwa [← hweight]
private theorem locallyConstant_weightedFiberSum_of_finite_open_chart
    {X Y U V : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y)
    (comm : h ≫ f = π ≫ g)
    [IsFinite π] [IsOpenImmersion (pullback.lift h π comm)]
    (w : X → ℤ) (hw : IsWeighting f w) :
    IsLocallyConstant (separableDegreeWeightedFiberSum π (w ∘ h)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro v
  have hfinite : ∀ t, (π ⁻¹' {t}).Finite := fun t ↦ π.finite_preimage_singleton t
  obtain ⟨n, x, hx, hxi⟩ := exists_fin_bijective_isolated_fiber π hfinite v
  obtain ⟨E, m, D, d, hdisj, hcover, hclopen, hspec, hnone⟩ :=
    exists_etaleNeighborhood_purelyInseparable_decomposition
      π n v x hx.1 hxi
  let q : E.scheme ⟶ V := E.toBase
  let P := pullback π q
  let πP : P ⟶ E.scheme := pullback.snd π q
  let wP : P → ℤ := (w ∘ h) ∘ pullback.fst π q
  let F (z : Option (Σ i : Fin n, Fin (m i))) : E.scheme → ℤ :=
    separableDegreeWeightedFiberSum ((D z).ι ≫ πP) (wP ∘ (D z).ι)
  have hpieces : ∀ z, ∀ᶠ t in 𝓝 E.point, F z t = F z E.point := by
    intro z
    cases z with
    | none =>
      have hempty := fiber_eq_empty_of_forall_ne
        π v x hx.2 E (D none) hnone
      have hzero := separableDegreeWeightedFiberSum_eventually_eq_zero
        πP (D none) (hclopen none).1 E.point hempty (wP ∘ (D none).ι)
      filter_upwards [hzero] with t ht
      rwa [show F none E.point = 0 from hzero.self_of_nhds]
    | some z =>
      obtain ⟨i, j⟩ := z
      obtain ⟨hfin, hfiber, _, ⟨hvu, hpure⟩⟩ := hspec i j
      have : IsFinite ((D (some ⟨i, j⟩)).ι ≫ πP) := hfin
      have hevent := eventually_eq_weightedFiberSum_of_singleton_open_piece
        f h π g comm q (D (some ⟨i, j⟩)) (d i j)
        E.point hvu hfiber hpure w hw
      simpa only [F, wP, πP, Function.comp_assoc] using hevent
  have hdisj' : ∀ i j, i ≠ j → Disjoint (D i : Set P) (D j : Set P) :=
    fun i j hij ↦ hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hcover' : ∀ p : P, ∃ i, p ∈ D i := fun p ↦
    Set.mem_iUnion.mp (show p ∈ ⋃ i, (D i).1 by rw [hcover]; trivial)
  have : IsFinite πP := by dsimp [πP]; infer_instance
  have hpartition := separableDegreeWeightedFiberSum_eq_sum_opens
    πP wP D hdisj' hcover' (fun t ↦ πP.finite_preimage_singleton t)
  have hlocalP : ∀ᶠ t in 𝓝 E.point,
      separableDegreeWeightedFiberSum πP wP t =
        separableDegreeWeightedFiberSum πP wP E.point := by
    simpa only [hpartition, F, Finset.sum_apply] using
      eventually_eq_finset_sum Finset.univ F E.point fun z _ ↦ hpieces z
  have hbase := separableDegreeWeightedFiberSum_comp_of_isPullback
    π (pullback.fst π q) πP q (IsPullback.of_hasPullback π q)
    hfinite (w ∘ h)
  have hlocalComp : ∀ᶠ t in 𝓝 E.point,
      separableDegreeWeightedFiberSum π (w ∘ h) (q t) =
        separableDegreeWeightedFiberSum π (w ∘ h) (q E.point) := by
    have hpoint (t : E.scheme) :
        separableDegreeWeightedFiberSum π (w ∘ h) (q t) =
          separableDegreeWeightedFiberSum πP wP t := by
      simpa only [Function.comp_apply, wP] using congrFun hbase t
    filter_upwards [hlocalP] with t ht
    calc
      separableDegreeWeightedFiberSum π (w ∘ h) (q t) =
          separableDegreeWeightedFiberSum πP wP t := hpoint t
      _ = separableDegreeWeightedFiberSum πP wP E.point := ht
      _ = separableDegreeWeightedFiberSum π (w ∘ h) (q E.point) :=
        (hpoint E.point).symm
  have : Etale q := inferInstance
  have hlocalV := eventually_eq_of_openMap_comp q q.isOpenMap
    (separableDegreeWeightedFiberSum π (w ∘ h)) E.point hlocalComp
  simpa only [q, E.map_point] using hlocalV

/-- A weighting pulls back to a weighting along an arbitrary base change. -/
@[stacks 0F3B, sga "4 XVII 6.2.4" "base change"]
theorem IsWeighting.comp_of_isPullback {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
    {w : X → ℤ} (hw : IsWeighting f w)
    (sq : IsPullback p f' f g) [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    IsWeighting f' (w ∘ p) := by
  intro U V h π k comm hk hU hπ
  let h₀ : U ⟶ X := h ≫ p
  let g₀ : V ⟶ Y := k ≫ g
  have comm₀ : h₀ ≫ f = π ≫ g₀ := by
    dsimp [h₀, g₀]
    simp only [Category.assoc, sq.w, reassoc_of% comm]
  let e : pullback f' k ≅ pullback f (k ≫ g) :=
    ((IsPullback.of_hasPullback f' k).paste_horiz sq).isoIsPullback _ _
      (IsPullback.of_hasPullback f (k ≫ g))
  have he₁ : e.hom ≫ pullback.fst f (k ≫ g) = pullback.fst f' k ≫ p := by simp [e]
  have he₂ : e.hom ≫ pullback.snd f (k ≫ g) = pullback.snd f' k := by simp [e]
  have hlift :
      pullback.lift h π comm ≫ e.hom = pullback.lift h₀ π comm₀ := by
    apply pullback.hom_ext
    · calc
        pullback.lift h π comm ≫ e.hom ≫ pullback.fst f (k ≫ g) =
            pullback.lift h π comm ≫ (pullback.fst f' k ≫ p) := by rw [he₁]
        _ = h₀ := by
          show (pullback.lift h π comm ≫ pullback.fst f' k) ≫ p = h ≫ p
          rw [pullback.lift_fst]
        _ = pullback.lift h₀ π comm₀ ≫ pullback.fst f (k ≫ g) := by
          rw [pullback.lift_fst]
    · calc
        pullback.lift h π comm ≫ e.hom ≫ pullback.snd f (k ≫ g) =
            pullback.lift h π comm ≫ pullback.snd f' k := by rw [he₂]
        _ = π := by
          rw [pullback.lift_snd]
        _ = pullback.lift h₀ π comm₀ ≫ pullback.snd f (k ≫ g) := by
          rw [pullback.lift_snd]
  have : IsOpenImmersion (pullback.lift h₀ π comm₀) := by
    rw [← hlift]
    infer_instance
  have : IsFinite π := hπ
  exact locallyConstant_weightedFiberSum_of_finite_open_chart f h₀ π g₀ comm₀ w hw
end AlgebraicGeometry
