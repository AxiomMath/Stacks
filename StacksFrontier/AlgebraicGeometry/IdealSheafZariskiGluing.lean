module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.IdealSheafFromAffineFamily

/-!
# Gluing ideal sheaves along an open cover

Let `W` be a scheme and `{q i : V i ⟶ W}` a jointly surjective family of open immersions. Ideal
sheaves on the `V i` whose pullbacks to the overlaps `V i ×_W V j` agree glue to an ideal sheaf
on `W`, and an ideal sheaf on `W` is determined by its pullbacks to the `V i`. In other words,
quasi-coherent sheaves of ideals form a sheaf for the Zariski topology.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_preimage_of_le_opensRange`: for an open
  immersion `p` and an affine open `A` inside its range, the ideal of the pullback of `I` over
  `p ⁻¹ A` is the image of the ideal of `I` over `A` under the isomorphism `p.app A`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_comap_eq_of_isOpenImmersion`: an ideal sheaf
  is determined by its pullbacks along a jointly surjective family of open immersions.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion`: ideal sheaves on
  the members of such a family which agree on the overlaps glue.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Pulling an ideal back along the inverse of an isomorphism of commutative rings is pushing it
forward along the isomorphism. -/
private lemma comap_inv_eq_map {R S : CommRingCat.{u}} (e : R ≅ S) (K : Ideal R) :
    K.comap e.inv.hom = K.map e.hom.hom :=
  Ideal.comap_symm (I := K) e.commRingCatIsoToRingEquiv

/-- For an open immersion `p` and an open `A` of the target contained in the range of `p`, the map
`p.app A` is bijective. -/
private lemma bijective_app_of_le_opensRange {X Y : Scheme.{u}} (p : X ⟶ Y) [IsOpenImmersion p]
    (A : Y.Opens) (hA : A ≤ p.opensRange) : Function.Bijective (p.app A).hom := by
  have := p.isIso_app A hA
  exact ConcreteCategory.bijective_of_isIso _

/-- For an open immersion `p` and an affine open `A` of the target contained in the range of `p`,
the ideal of the pullback `I.comap p` over `p ⁻¹ A` is the image of the ideal of `I` over `A`
under the isomorphism `p.app A`. -/
theorem ideal_comap_preimage_of_le_opensRange {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (p : X ⟶ Y) [IsOpenImmersion p] (A : Y.affineOpens) (hA : A.1 ≤ p.opensRange)
    (hA' : IsAffineOpen (p ⁻¹ᵁ A.1) := A.2.preimage_of_isOpenImmersion p hA) :
    (I.comap p).ideal ⟨p ⁻¹ᵁ A.1, hA'⟩ =
      (I.ideal A).map (p.app A.1).hom := by
  have h : p ''ᵁ p ⁻¹ᵁ A.1 = A.1 := by
    rw [p.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hA]
  rw [ideal_comap_of_isOpenImmersion, comap_inv_eq_map]
  have e := I.map_ideal' (U := ⟨p ''ᵁ p ⁻¹ᵁ A.1, hA'.image_of_isOpenImmersion p⟩) (V := A)
    (homOfLE h.le).op
  refine (congrArg (Ideal.map (p.appIso (p ⁻¹ᵁ A.1)).hom.hom) e.symm).trans ?_
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
    Scheme.Hom.app_eq_appLE]

/-- The ideal of `I.comap p` over `p ⁻¹ A` determines the ideal of `I` over `A`, for an open
immersion `p` and an affine open `A` inside its range: it is its preimage under `p.app A`. -/
theorem ideal_eq_comap_ideal_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (p : X ⟶ Y) [IsOpenImmersion p] (A : Y.affineOpens) (hA : A.1 ≤ p.opensRange)
    (hA' : IsAffineOpen (p ⁻¹ᵁ A.1) := A.2.preimage_of_isOpenImmersion p hA) :
    I.ideal A = ((I.comap p).ideal ⟨p ⁻¹ᵁ A.1, hA'⟩).comap (p.app A.1).hom := by
  rw [ideal_comap_preimage_of_le_opensRange I p A hA hA',
    Ideal.comap_map_of_bijective _ (bijective_app_of_le_opensRange p A.1 hA)]

/-- Every point of `W` lying in the range of an open immersion `q` lies in an affine open of `W`
contained in that range. -/
private lemma exists_affineOpens_le_opensRange {W V : Scheme.{u}} (q : V ⟶ W)
    [IsOpenImmersion q] (v : V) :
    ∃ U : W.affineOpens, U.1 ≤ q.opensRange ∧ q v ∈ U.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (a := q v) (Set.mem_range_self v) q.opensRange.2
  exact ⟨⟨U, hU⟩, hle, hxU⟩

/-- **Ideal sheaves are determined by their pullbacks to an open cover.** Two ideal sheaves on
`W` whose pullbacks along a jointly surjective family of open immersions agree are equal. -/
theorem ext_of_comap_eq_of_isOpenImmersion {W : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}}
    (q : ∀ i, V i ⟶ W) [∀ i, IsOpenImmersion (q i)]
    (hq : ∀ w : W, ∃ i, ∃ v : V i, q i v = w) {J J' : W.IdealSheafData}
    (h : ∀ i, J.comap (q i) = J'.comap (q i)) : J = J' := by
  refine ext_of_iSup_eq_top (ι := {U : W.affineOpens // ∃ i, U.1 ≤ (q i).opensRange})
    (fun U ↦ U.1) ?_ fun ⟨U, i, hU⟩ ↦ ?_
  · refine eq_top_iff.mpr fun w _ ↦ ?_
    obtain ⟨i, v, rfl⟩ := hq w
    obtain ⟨U, hU, hvU⟩ := exists_affineOpens_le_opensRange (q i) v
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, i, hU⟩, hvU⟩
  · rw [ideal_eq_comap_ideal_comap J (q i) U hU, ideal_eq_comap_ideal_comap J' (q i) U hU, h i]

section Gluing

variable {W : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}} (q : ∀ i, V i ⟶ W)
  [∀ i, IsOpenImmersion (q i)] (I : ∀ i, (V i).IdealSheafData)

/-- The candidate ideal over an affine open `U` of `W` contained in the range of `q i`: the
preimage of the ideal of `I i` over `q i ⁻¹ U` under the isomorphism `(q i).app U`. -/
private def localIdeal (i : ι) (U : W.affineOpens) (hU : U.1 ≤ (q i).opensRange) :
    Ideal Γ(W, U) :=
  ((I i).ideal ⟨q i ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion (q i) hU⟩).comap
    ((q i).app U.1).hom

/-- Pushing the candidate ideal forward along `(q i).app U` recovers the ideal of `I i`. -/
private lemma map_localIdeal (i : ι) (U : W.affineOpens) (hU : U.1 ≤ (q i).opensRange) :
    (localIdeal q I i U hU).map ((q i).app U.1).hom =
      (I i).ideal ⟨q i ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion (q i) hU⟩ := by
  exact Ideal.map_comap_of_surjective _ (bijective_app_of_le_opensRange (q i) U.1 hU).2 _

/-- The candidate ideal computed through a composite open immersion `r = p ≫ q'` and the pullback
of the ideal sheaf along `p` agrees with the one computed through `q'`. -/
private lemma comap_ideal_comap_eq {P X : Scheme.{u}} (p : P ⟶ X) (q' : X ⟶ W) (r : P ⟶ W)
    [IsOpenImmersion p] [IsOpenImmersion q'] [IsOpenImmersion r] (hr : p ≫ q' = r)
    (K : X.IdealSheafData) (U : W.affineOpens) (hU : U.1 ≤ r.opensRange)
    (hU' : U.1 ≤ q'.opensRange) :
    ((K.comap p).ideal ⟨r ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion r hU⟩).comap
        (r.app U.1).hom =
      (K.ideal ⟨q' ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion q' hU'⟩).comap (q'.app U.1).hom := by
  subst hr
  have hle : q' ⁻¹ᵁ U.1 ≤ p.opensRange := fun x hx ↦
    (hU hx).imp fun z hz ↦ q'.isOpenEmbedding.injective (by simpa using hz)
  have e := ideal_comap_preimage_of_le_opensRange K p
    ⟨q' ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion q' hU'⟩ hle
    (U.2.preimage_of_isOpenImmersion (p ≫ q') hU)
  refine (congrArg (Ideal.comap ((p ≫ q').app U.1).hom) e).trans ?_
  show Ideal.comap ((p.app (q' ⁻¹ᵁ U.1)).hom.comp (q'.app U.1).hom)
    (Ideal.map (p.app (q' ⁻¹ᵁ U.1)).hom _) = _
  rw [← Ideal.comap_comap,
    Ideal.comap_map_of_bijective _ (bijective_app_of_le_opensRange p _ hle)]

variable {q I} in
/-- Under the compatibility on overlaps, the candidate ideal does not depend on the member of the
cover used to compute it. -/
private lemma localIdeal_eq
    (h : ∀ i j, (I i).comap (pullback.fst (q i) (q j)) =
      (I j).comap (pullback.snd (q i) (q j)))
    (i j : ι) (U : W.affineOpens) (hi : U.1 ≤ (q i).opensRange)
    (hj : U.1 ≤ (q j).opensRange) :
    localIdeal q I i U hi = localIdeal q I j U hj := by
  have hr : U.1 ≤ (pullback.fst (q i) (q j) ≫ q i).opensRange := by
    intro w hw
    obtain ⟨a, ha⟩ := hi hw
    obtain ⟨b, hb⟩ := hj hw
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
    exact ⟨z, by simpa [hz] using ha⟩
  rw [localIdeal, localIdeal,
    ← comap_ideal_comap_eq (pullback.fst (q i) (q j)) (q i) _ rfl (I i) U hr hi,
    ← comap_ideal_comap_eq (pullback.snd (q i) (q j)) (q j) _ pullback.condition.symm (I j) U hr
      hj, h i j]

/-- The ideal over an affine open `U` of the glued ideal sheaf: the infimum of the candidate
ideals over all members of the cover whose range contains `U`. -/
private def gluedIdeal (U : W.affineOpens) : Ideal Γ(W, U) :=
  ⨅ (i : ι) (hU : U.1 ≤ (q i).opensRange), localIdeal q I i U hU

variable {q I} in
/-- Under the compatibility on overlaps, the glued ideal over `U` is the candidate ideal computed
through any member of the cover whose range contains `U`. -/
private lemma gluedIdeal_eq
    (h : ∀ i j, (I i).comap (pullback.fst (q i) (q j)) =
      (I j).comap (pullback.snd (q i) (q j)))
    (i : ι) (U : W.affineOpens) (hU : U.1 ≤ (q i).opensRange) :
    gluedIdeal q I U = localIdeal q I i U hU :=
  le_antisymm (iInf₂_le i hU)
    (le_iInf₂ fun j hj ↦ (localIdeal_eq h i j U hU hj).le)

/-- The candidate ideals computed through a fixed member of the cover are compatible with
restriction. -/
private lemma map_localIdeal_restrict (i : ι) (U U' : W.affineOpens) (hU'U : U' ≤ U)
    (hU : U.1 ≤ (q i).opensRange) :
    (localIdeal q I i U hU).map (W.presheaf.map (homOfLE hU'U).op).hom =
      localIdeal q I i U' (le_trans hU'U hU) := by
  have hU' : U'.1 ≤ (q i).opensRange := le_trans hU'U hU
  have hb := bijective_app_of_le_opensRange (q i) U'.1 hU'
  have hinj : Function.Injective (Ideal.map ((q i).app U'.1).hom) := fun K L e ↦ by
    rw [← Ideal.comap_map_of_bijective _ hb (I := K), e, Ideal.comap_map_of_bijective _ hb]
  refine hinj ?_
  rw [map_localIdeal, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.naturality,
    CommRingCat.hom_comp, ← Ideal.map_map, map_localIdeal]
  exact (I i).map_ideal' (U := ⟨q i ⁻¹ᵁ U'.1, U'.2.preimage_of_isOpenImmersion (q i) hU'⟩)
    (V := ⟨q i ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion (q i) hU⟩) _

variable {q} in
/-- An affine open of `W` is small if it is contained in the range of some `q i`. -/
private def IsSmall (U : W.affineOpens) : Prop := ∃ i, U.1 ≤ (q i).opensRange

end Gluing

/-- **Ideal sheaves glue along an open cover.** Let `{q i : V i ⟶ W}` be a jointly surjective
family of open immersions and `I i` an ideal sheaf on `V i` for each `i`, such that the pullbacks
of `I i` and `I j` to `V i ×_W V j` agree. Then there is an ideal sheaf on `W` whose pullback to
each `V i` is `I i`. -/
theorem exists_comap_eq_of_isOpenImmersion {W : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}}
    (q : ∀ i, V i ⟶ W) [∀ i, IsOpenImmersion (q i)]
    (hq : ∀ w : W, ∃ i, ∃ v : V i, q i v = w)
    (I : ∀ i, (V i).IdealSheafData)
    (h : ∀ i j, (I i).comap (pullback.fst (q i) (q j)) =
      (I j).comap (pullback.snd (q i) (q j))) :
    ∃ J : W.IdealSheafData, ∀ i, J.comap (q i) = I i := by
  have hcover : ∀ w : W, ∃ U : W.affineOpens, IsSmall (q := q) U ∧ w ∈ U.1 := by
    intro w
    obtain ⟨i, v, rfl⟩ := hq w
    obtain ⟨U, hU, hvU⟩ := exists_affineOpens_le_opensRange (q i) v
    exact ⟨U, ⟨i, hU⟩, hvU⟩
  have hbasic : ∀ (U : W.affineOpens) (f : Γ(W, U)), IsSmall (q := q) U →
      IsSmall (q := q) (W.affineBasicOpen f) :=
    fun U f ⟨i, hU⟩ ↦ ⟨i, le_trans (W.basicOpen_le f) hU⟩
  have hcompat : ∀ (U U' : W.affineOpens) (hle : U' ≤ U), IsSmall (q := q) U →
      IsSmall (q := q) U' →
      (gluedIdeal q I U).map (W.presheaf.map (homOfLE hle).op).hom = gluedIdeal q I U' := by
    rintro U U' hle ⟨i, hU⟩ -
    rw [gluedIdeal_eq h i U hU, gluedIdeal_eq h i U' (le_trans hle hU),
      map_localIdeal_restrict]
  refine ⟨ofAffineFamily IsSmall (gluedIdeal q I) hcover hbasic hcompat, fun k ↦ ?_⟩
  refine ext_of_iSup_eq_top
    (ι := {U : W.affineOpens // U.1 ≤ (q k).opensRange})
    (fun U ↦ ⟨q k ⁻¹ᵁ U.1.1, U.1.2.preimage_of_isOpenImmersion (q k) U.2⟩) ?_ fun ⟨U, hU⟩ ↦ ?_
  · refine eq_top_iff.mpr fun v _ ↦ ?_
    obtain ⟨U, hU, hvU⟩ := exists_affineOpens_le_opensRange (q k) v
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hvU⟩
  · rw [ideal_comap_preimage_of_le_opensRange _ (q k) U hU,
      ideal_ofAffineFamily IsSmall (gluedIdeal q I) hcover hbasic hcompat ⟨k, hU⟩,
      gluedIdeal_eq h k U hU, map_localIdeal]

end AlgebraicGeometry.Scheme.IdealSheafData

end
