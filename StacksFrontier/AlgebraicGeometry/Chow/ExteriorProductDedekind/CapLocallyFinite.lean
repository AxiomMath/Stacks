module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Reduction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRule

/-!
# Capping with a bivariant class commutes with locally finite sums

Let `c ∈ A^p(X ⟶ Y)` be a bivariant class and let `g : W ⟶ Y` be a test scheme. A cycle on `W`
which is the locally finite sum `A = ∑ᵢ (jᵢ)_* aᵢ` of pushforwards along a locally finite family
of closed immersions `jᵢ : Wᵢ ⟶ W` satisfies

  `c ∩ [A] = [∑ᵢ (j'ᵢ)_* bᵢ]`   where   `[bᵢ] = c ∩ [aᵢ]`

and `j'ᵢ : Wᵢ ×_Y X ⟶ W ×_Y X` are the base changes of the `jᵢ`.

## Main results

* `Stacks.Chow.mem_rationalEquivalences_of_finsum_isClosedImmersion`: a locally finite sum of
  pushforwards along closed immersions of cycles rationally equivalent to zero is rationally
  equivalent to zero.
* `Stacks.Chow.BivariantClass.cap_mk_eq_mk_of_locallyFinite`: capping commutes with a locally
  finite sum of pushforwards along closed immersions.
* `Stacks.Chow.BivariantClass.cap_chowGroupCongr_mk_eq_mk_of_locallyFinite`: the same, with the
  test morphisms and the structure morphisms of the pieces given separately.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Pushforwards and restrictions of cycles -/

section Bookkeeping

variable {C : ChowSituation.{u}}

/-- Pushforward along an endomorphism equal to the identity is the transport along the equality
of the two structure morphisms. -/
theorem chowPushforwardOfIso_of_eq_id {A : Scheme.{u}} (sA sA' : A ⟶ C.S)
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (e : A ⟶ A) [IsIso e] (he : e ≫ sA' = sA)
    (h : e = 𝟙 A) (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sA' e he k x =
      chowGroupCongr C (by rw [← he, h, Category.id_comp]) k x := by
  subst h
  obtain rfl : sA' = sA := by rw [← he, Category.id_comp]
  exact chowPushforwardOfIso_id C sA' k x

/-- The base change of a closed immersion of test schemes is a closed immersion. -/
instance isClosedImmersion_testBaseChangeMapOfEq {Y Z T T' : Scheme.{u}} (w : Y ⟶ Z)
    (g : T ⟶ Z) (v : T' ⟶ T) [IsClosedImmersion v] (m : T' ⟶ Z) (hm : v ≫ g = m) :
    IsClosedImmersion (testBaseChangeMapOfEq w g v m hm) :=
  MorphismProperty.of_isPullback (isPullback_testBaseChangeMapOfEq w g v m hm)
    (P := @IsClosedImmersion) inferInstance

/-- A locally finite sum of pushforwards along closed immersions of cycles rationally equivalent
to zero is rationally equivalent to zero, with the structure morphisms of the pieces given
separately. -/
theorem mem_rationalEquivalences_of_finsum_isClosedImmersion {X : Scheme.{u}} (s : X ⟶ C.S)
    [LocallyOfFiniteType s] (k : ℤ) {I : Type u} {Z : I → Scheme.{u}} (j : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (j i)] (hfinite : LocallyFinite fun i ↦ Set.range (j i))
    (sZ : ∀ i, Z i ⟶ C.S) [∀ i, LocallyOfFiniteType (sZ i)] (hs : ∀ i, j i ≫ s = sZ i)
    (a : ∀ i, CycleGroup C (sZ i) k) (ha : ∀ i, a i ∈ rationalEquivalences C (sZ i) k)
    (α : CycleGroup C s k)
    (hα : ∀ x, α.1 x = ∑ᶠ i, (properPushforward C (sZ i) s (j i) (hs i) k (a i)).1 x) :
    α ∈ rationalEquivalences C s k := by
  obtain rfl : sZ = fun i ↦ j i ≫ s := funext fun i ↦ (hs i).symm
  exact rationallyEquivalentToZero_finsum_of_isClosedImmersion C s k j hfinite a ha α hα

/-- A cycle is the locally finite sum of the pushforwards of its restrictions to the pieces of a
decomposition into open and closed subschemes presented by open immersions. -/
theorem cycle_eq_finsum_properPushforward_cycleGroupRestrict {X : Scheme.{u}} (s : X ⟶ C.S)
    [LocallyOfFiniteType s] (k : ℤ) {I : Type u} {Z : I → Scheme.{u}} (m : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (m i)] [∀ i, IsClosedImmersion (m i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (m i))
    (hdisjoint : Pairwise fun i l ↦ Disjoint (Set.range (m i)) (Set.range (m l)))
    (sZ : ∀ i, Z i ⟶ C.S) [∀ i, LocallyOfFiniteType (sZ i)] (hs : ∀ i, m i ≫ s = sZ i)
    (c : CycleGroup C s k) (x : X) :
    c.1 x = ∑ᶠ i, (properPushforward C (sZ i) s (m i) (hs i) k
      (cycleGroupRestrict C s (sZ i) (m i) (hs i) k c)).1 x := by
  classical
  obtain ⟨i₀, z, rfl⟩ := hcover x
  rw [finsum_eq_single _ i₀]
  · rw [properPushforward_apply_image_of_isClosedImmersion, cycleGroupRestrict_apply]
  · exact fun i hi ↦ properPushforward_apply_of_notMem_range C _ _ _ _ _ _
      fun h ↦ Set.disjoint_left.1 (hdisjoint hi) h ⟨z, rfl⟩

/-- The proper pushforward of a cycle is the locally finite sum of the pushforwards of its
restrictions to the pieces of a decomposition into open and closed subschemes. -/
private theorem properPushforward_apply_eq_finsum_cycleGroupRestrict {X X' : Scheme.{u}}
    (s : X ⟶ C.S) [LocallyOfFiniteType s] (s' : X' ⟶ C.S) [LocallyOfFiniteType s'] (π : X ⟶ X')
    [IsProper π] (hπ : π ≫ s' = s) (k : ℤ) {I : Type u} {Z : I → Scheme.{u}} (m : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (m i)] [∀ i, IsClosedImmersion (m i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (m i))
    (hdisjoint : Pairwise fun i l ↦ Disjoint (Set.range (m i)) (Set.range (m l)))
    (sZ : ∀ i, Z i ⟶ C.S) [∀ i, LocallyOfFiniteType (sZ i)] (hs : ∀ i, m i ≫ s = sZ i)
    (c : CycleGroup C s k) (z : X') :
    (properPushforward C s s' π hπ k c).1 z = ∑ᶠ i, (properPushforward C (sZ i) s' (m i ≫ π)
      (by rw [Category.assoc, hπ, hs i]) k
      (cycleGroupRestrict C s (sZ i) (m i) (hs i) k c)).1 z := by
  have hsum := cycle_eq_finsum_properPushforward_cycleGroupRestrict s k m hcover hdisjoint sZ hs c
  have hmap := algebraicCycle_map_finsum_apply π (relativeDimension C.dimensionFunction s)
    (relativeDimension C.dimensionFunction s') (fun i ↦ Set.range (m i))
    (Stacks.Topology.locallyFinite_of_disjoint_open_cover _
      (fun i ↦ (m i).isOpenEmbedding.isOpen_range) hcover hdisjoint)
    (fun i ↦ (properPushforward C (sZ i) s (m i) (hs i) k
      (cycleGroupRestrict C s (sZ i) (m i) (hs i) k c)).1)
    (fun i ↦ support_properPushforward_subset C _ _ _ _ k _) c.1 hsum z
  refine hmap.trans (finsum_congr fun i ↦ ?_)
  exact congrArg (fun e ↦ e.1 z)
    (properPushforward_properPushforward C (sZ i) s s' (m i) π (hs i) hπ k _)

end Bookkeeping

/-! ### Capping and locally finite sums -/

section LocallyFinite

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}

/-- The base change of an open immersion of test schemes is an open immersion. -/
instance isOpenImmersion_testBaseChangeMapOfEq {Y Z T T' : Scheme.{u}} (w : Y ⟶ Z)
    (g : T ⟶ Z) (v : T' ⟶ T) [IsOpenImmersion v] (m : T' ⟶ Z) (hm : v ≫ g = m) :
    IsOpenImmersion (testBaseChangeMapOfEq w g v m hm) :=
  MorphismProperty.of_isPullback (isPullback_testBaseChangeMapOfEq w g v m hm)
    (P := @IsOpenImmersion) inferInstance

/-- The range of the base change of a morphism of test schemes is the inverse image of its
range. -/
theorem range_testBaseChangeMapOfEq {Y Z T T' : Scheme.{u}} (w : Y ⟶ Z) (g : T ⟶ Z)
    (v : T' ⟶ T) (m : T' ⟶ Z) (hm : v ≫ g = m) :
    Set.range (testBaseChangeMapOfEq w g v m hm) = pullback.snd w g ⁻¹' Set.range v := by
  have hsq := isPullback_testBaseChangeMapOfEq w g v m hm
  have hsnd : hsq.isoPullback.hom ≫ pullback.snd v (pullback.snd w g) =
      testBaseChangeMapOfEq w g v m hm := hsq.isoPullback_hom_snd
  have hsurj : Function.Surjective hsq.isoPullback.hom := Surjective.surj
  rw [← hsnd, show Set.range ((hsq.isoPullback.hom ≫ pullback.snd v (pullback.snd w g))) =
      Set.range ((pullback.snd v (pullback.snd w g)) ∘ hsq.isoPullback.hom) from rfl,
    Set.range_comp, hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_snd]

/-- Let `jᵢ : Vᵢ ⟶ W` be a locally finite family of closed immersions into a test scheme
`g : W ⟶ Y`, let `A = ∑ᵢ (jᵢ)_* aᵢ` and let `B = ∑ᵢ (j'ᵢ)_* bᵢ` on `W ×_Y X`, where `j'ᵢ` is the
base change of `jᵢ` and `[bᵢ] = c ∩ [aᵢ]`. Then `c ∩ [A] = [B]`. -/
theorem BivariantClass.cap_mk_eq_mk_of_locallyFinite (c : BivariantClass C G sX sY f hf p)
    {W : Scheme.{u}} (g : W ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) {I : Type u}
    {V : I → Scheme.{u}} (j : ∀ i, V i ⟶ W) [∀ i, IsClosedImmersion (j i)]
    (hfin : LocallyFinite fun i ↦ Set.range (j i))
    (a : ∀ i, CycleGroup C ((j i ≫ g) ≫ sY) k) (A : CycleGroup C (g ≫ sY) k)
    (hA : ∀ z, A.1 z = ∑ᶠ i, (properPushforward C ((j i ≫ g) ≫ sY) (g ≫ sY) (j i)
      (Category.assoc _ _ _).symm k (a i)).1 z)
    (b : ∀ i, CycleGroup C (pullback.fst f (j i ≫ g) ≫ sX) (k - p))
    (hb : ∀ i, QuotientAddGroup.mk' (rationalEquivalences C _ (k - p)) (b i) =
      c.cap (j i ≫ g) k (QuotientAddGroup.mk' (rationalEquivalences C _ k) (a i)))
    (B : CycleGroup C (pullback.fst f g ≫ sX) (k - p))
    (hB : ∀ z, B.1 z = ∑ᶠ i, (properPushforward C (pullback.fst f (j i ≫ g) ≫ sX)
      (pullback.fst f g ≫ sX) (bivariantBaseChangeMap f g (j i))
      (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) (k - p) (b i)).1 z) :
    c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) A) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ sX) (k - p)) B := by
  classical
  have hproper : IsProper (Sigma.desc j) := isProper_sigmaDesc_of_locallyFinite V j hfin
  set π := Sigma.desc j with hπ
  have hιπ : ∀ i, Sigma.ι V i ≫ π = j i := fun i ↦ Sigma.ι_desc j i
  have hcl : ∀ i, IsClosedImmersion (Sigma.ι V i) := isClosedImmersion_sigmaι V
  have hstrV : ∀ i, Sigma.ι V i ≫ ((π ≫ g) ≫ sY) = (j i ≫ g) ≫ sY := fun i ↦ by
    rw [← hιπ i]; simp
  obtain ⟨Ã, hÃ⟩ := exists_cycleGroup_of_sigma C V ((π ≫ g) ≫ sY)
    (fun i ↦ (j i ≫ g) ≫ sY) hstrV k a
  have hres : ∀ i, cycleGroupRestrict C ((π ≫ g) ≫ sY) ((j i ≫ g) ≫ sY) (Sigma.ι V i)
      (hstrV i) k Ã = a i := fun i ↦
    Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ by
      rw [cycleGroupRestrict_apply]; exact hÃ i x)
  have hpushA : properPushforward C ((π ≫ g) ≫ sY) (g ≫ sY) π (Category.assoc _ _ _).symm k Ã = A
      := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [hA z]
    refine (properPushforward_apply_eq_finsum_cycleGroupRestrict _ _ π _ k (Sigma.ι V)
      (exists_mem_range_sigmaι V) (pairwise_disjoint_range_sigmaι V)
      (fun i ↦ (j i ≫ g) ≫ sY) hstrV Ã z).trans (finsum_congr fun i ↦ ?_)
    rw [hres i, properPushforward_congr C _ _ _ (j i) (hιπ i)]
  have hfstπ : bivariantBaseChangeMap f g π ≫ (pullback.fst f g ≫ sX) =
      pullback.fst f (π ≫ g) ≫ sX := by
    rw [← Category.assoc, bivariantBaseChangeMap_fst]
  have hnat := c.proper_naturality g π (bivariantBaseChangeMap f g π)
    (isPullback_bivariantBaseChangeMap f g π) (bivariantBaseChangeMap_fst f g π) k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C ((π ≫ g) ≫ sY) (g ≫ sY) π
      (Category.assoc _ _ _).symm k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
      (pullback.fst f (π ≫ g) ≫ sX) (pullback.fst f g ≫ sX) (bivariantBaseChangeMap f g π)
      hfstπ (k - p))
    (QuotientAddGroup.mk' (rationalEquivalences C ((π ≫ g) ≫ sY) k) Ã)
  rw [properChowPushforward_mk, hpushA] at hnat
  rw [hnat]
  obtain ⟨δ, hδ⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C _ (k - p))
    (c.cap (π ≫ g) k (QuotientAddGroup.mk' (rationalEquivalences C ((π ≫ g) ≫ sY) k) Ã))
  have hιg : ∀ i, Sigma.ι V i ≫ π ≫ g = j i ≫ g := fun i ↦ by rw [← Category.assoc, hιπ]
  set v' : ∀ i, pullback f (j i ≫ g) ⟶ pullback f (π ≫ g) := fun i ↦
    testBaseChangeMapOfEq f (π ≫ g) (Sigma.ι V i) (j i ≫ g) (hιg i) with hv'
  have hv'base : ∀ i, v' i ≫ (pullback.fst f (π ≫ g) ≫ sX) = pullback.fst f (j i ≫ g) ≫ sX :=
    fun i ↦ by rw [← Category.assoc, hv', testBaseChangeMapOfEq_fst]
  have hrange : ∀ i, Set.range (v' i) = pullback.snd f (π ≫ g) ⁻¹' Set.range (Sigma.ι V i) :=
    fun i ↦ range_testBaseChangeMapOfEq _ _ _ _ _
  have hcover : ∀ x : (pullback f (π ≫ g) : Scheme.{u}), ∃ i, x ∈ Set.range (v' i) :=
    fun x ↦ (exists_mem_range_sigmaι V (pullback.snd f (π ≫ g) x)).imp fun i hi ↦
      (hrange i).symm ▸ hi
  have hdisj : Pairwise fun i l ↦ Disjoint (Set.range (v' i)) (Set.range (v' l)) := by
    intro i l hil
    rw [hrange i, hrange l]
    exact (pairwise_disjoint_range_sigmaι V hil).preimage _
  have hpiece : ∀ i, QuotientAddGroup.mk' (rationalEquivalences C _ (k - p))
      (cycleGroupRestrict C (pullback.fst f (π ≫ g) ≫ sX) (pullback.fst f (j i ≫ g) ≫ sX)
        (v' i) (hv'base i) (k - p) δ) =
      QuotientAddGroup.mk' (rationalEquivalences C _ (k - p)) (b i) := fun i ↦ by
    rw [← chowGroupRestrict_mk, hδ, hb i,
      BivariantClass.cap_chowGroupRestrict C G sX sY f hf p c (π ≫ g) (Sigma.ι V i) (j i ≫ g)
        (hιg i) (v' i) (isPullback_testBaseChangeMapOfEq _ _ _ _ _)
        (testBaseChangeMapOfEq_fst _ _ _ _ _) k (hstrV i) (hv'base i),
      chowGroupRestrict_mk, hres i]
  have hcomp : ∀ i, v' i ≫ bivariantBaseChangeMap f g π = bivariantBaseChangeMap f g (j i) :=
    fun i ↦ pullback.hom_ext (by simp [hv']) (by simp [hv', ← hιπ i])
  have hj'base : ∀ i, bivariantBaseChangeMap f g (j i) ≫ (pullback.fst f g ≫ sX) =
      pullback.fst f (j i ≫ g) ≫ sX := fun i ↦ by
    rw [← Category.assoc, bivariantBaseChangeMap_fst]
  have hfin' : LocallyFinite fun i ↦ Set.range (bivariantBaseChangeMap f g (j i)) :=
    (hfin.preimage_continuous (pullback.snd f g).continuous).subset fun i ↦ by
      rw [range_bivariantBaseChangeMap]
  have hπδ : ∀ z, (properPushforward C (pullback.fst f (π ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
      (bivariantBaseChangeMap f g π) hfstπ (k - p) δ).1 z =
      ∑ᶠ i, (properPushforward C (pullback.fst f (j i ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
        (bivariantBaseChangeMap f g (j i)) (hj'base i) (k - p)
        (cycleGroupRestrict C (pullback.fst f (π ≫ g) ≫ sX) (pullback.fst f (j i ≫ g) ≫ sX)
          (v' i) (hv'base i) (k - p) δ)).1 z := by
    intro z
    refine (properPushforward_apply_eq_finsum_cycleGroupRestrict _ _ _ hfstπ (k - p) v' hcover
      hdisj (fun i ↦ pullback.fst f (j i ≫ g) ≫ sX) hv'base δ z).trans
      (finsum_congr fun i ↦ ?_)
    rw [properPushforward_congr C _ _ _ (bivariantBaseChangeMap f g (j i)) (hcomp i)]
  rw [← hδ, properChowPushforward_mk, eq_comm, ← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).2 <|
    mem_rationalEquivalences_of_finsum_isClosedImmersion (pullback.fst f g ≫ sX) (k - p)
    (fun i ↦ bivariantBaseChangeMap f g (j i)) hfin' (fun i ↦ pullback.fst f (j i ≫ g) ≫ sX)
    hj'base (fun i ↦ b i - cycleGroupRestrict C (pullback.fst f (π ≫ g) ≫ sX)
      (pullback.fst f (j i ≫ g) ≫ sX) (v' i) (hv'base i) (k - p) δ) (fun i ↦ ?_) _ (fun z ↦ ?_)
  · refine (QuotientAddGroup.eq_zero_iff (N := rationalEquivalences C _ (k - p)) _).1 ?_
    rw [QuotientAddGroup.mk_sub]
    exact sub_eq_zero.2 (hpiece i).symm
  · have hfinz : ∀ e : ∀ i, CycleGroup C (pullback.fst f (j i ≫ g) ≫ sX) (k - p),
        (Function.support fun i ↦ (properPushforward C (pullback.fst f (j i ≫ g) ≫ sX)
          (pullback.fst f g ≫ sX) (bivariantBaseChangeMap f g (j i)) (hj'base i) (k - p)
          (e i)).1 z).Finite := fun e ↦
      (hfin'.point_finite z).subset fun i hi ↦
        support_properPushforward_subset C _ _ _ _ (k - p) (e i) hi
    change B.1 z - (properPushforward C (pullback.fst f (π ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
      (bivariantBaseChangeMap f g π) hfstπ (k - p) δ).1 z = _
    rw [hB z, hπδ z, ← finsum_sub_distrib (hfinz b) (hfinz _)]
    refine finsum_congr fun i ↦ ?_
    rw [properPushforward_sub]
    rfl

/-- Capping commutes with locally finite sums of pushforwards along closed immersions, with the
test morphisms and the structure morphisms of the pieces given separately. -/
theorem BivariantClass.cap_chowGroupCongr_mk_eq_mk_of_locallyFinite
    (c : BivariantClass C G sX sY f hf p) {W : Scheme.{u}} (g : W ⟶ Y) [LocallyOfFiniteType g]
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (hsW : g ≫ sY = sW) (k : ℤ) {I : Type u}
    {V : I → Scheme.{u}} (j : ∀ i, V i ⟶ W) [∀ i, IsClosedImmersion (j i)]
    (hfin : LocallyFinite fun i ↦ Set.range (j i)) (gV : ∀ i, V i ⟶ Y)
    [∀ i, LocallyOfFiniteType (gV i)] (hgV : ∀ i, j i ≫ g = gV i) (sV : ∀ i, V i ⟶ C.S)
    [∀ i, LocallyOfFiniteType (sV i)] (hsV : ∀ i, j i ≫ sW = sV i)
    (a : ∀ i, CycleGroup C (sV i) k) (A : CycleGroup C sW k)
    (hA : ∀ z, A.1 z = ∑ᶠ i, (properPushforward C (sV i) sW (j i) (hsV i) k (a i)).1 z)
    (b : ∀ i, CycleGroup C (pullback.fst f (gV i) ≫ sX) (k - p))
    (hb : ∀ i, QuotientAddGroup.mk' (rationalEquivalences C _ (k - p)) (b i) =
      c.cap (gV i) k (chowGroupCongr C (by rw [← hsV i, ← hsW, ← hgV i, Category.assoc]) k
        (QuotientAddGroup.mk' (rationalEquivalences C _ k) (a i))))
    (B : CycleGroup C (pullback.fst f g ≫ sX) (k - p))
    (hB : ∀ z, B.1 z = ∑ᶠ i, (properPushforward C (pullback.fst f (gV i) ≫ sX)
      (pullback.fst f g ≫ sX) (testBaseChangeMapOfEq f g (j i) (gV i) (hgV i))
      (by rw [← Category.assoc, testBaseChangeMapOfEq_fst]) (k - p) (b i)).1 z) :
    c.cap g k (chowGroupCongr C hsW.symm k
        (QuotientAddGroup.mk' (rationalEquivalences C sW k) A)) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ sX) (k - p)) B := by
  subst hsW
  obtain rfl : sV = fun i ↦ j i ≫ g ≫ sY := funext fun i ↦ (hsV i).symm
  obtain rfl : gV = fun i ↦ j i ≫ g := funext fun i ↦ (hgV i).symm
  refine c.cap_mk_eq_mk_of_locallyFinite g k j hfin a A hA b hb B fun z ↦
    (hB z).trans (finsum_congr fun i ↦ ?_)
  rw [properPushforward_congr C _ _ _ (bivariantBaseChangeMap f g (j i))
    (pullback.hom_ext (by simp) (by simp))]

end LocallyFinite

end Stacks.Chow

end
