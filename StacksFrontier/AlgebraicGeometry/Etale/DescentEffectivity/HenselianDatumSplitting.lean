module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSectionsPushout
public import StacksFrontier.AlgebraicGeometry.Descent.IntegralEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.OpenSubDatum
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.TransitionSwap
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselianFinitePart
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductCriterion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair

/-!
# Splitting a descent datum along the splitting of its scheme over a henselian pair

Let `f : X ⟶ Spec A` be a finite morphism, let `I ⊆ A` be an ideal inside the Jacobson radical
of `A`, and let `(V, φ)` be a descent datum relative to `X/Spec A`. Let `V = W ⊔ W'` be a
splitting of `V` into two complementary opens, `W` finite over `Spec A` and `W'` carrying no point
above `Spec (A ⧸ I)`, as in the proof of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP). Then `W` and `W'` are invariant
under the gluing isomorphism, in the sense of
`AlgebraicGeometry.DescentDatum.IsTransitionInvariant`, and `(V, φ)` is the coproduct of the two
restricted descent data `AlgebraicGeometry.DescentDatum.restrictOpen`.

## Main results

* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_of_isFinite_of_isEmpty_closedFiber`:
  **the gluing isomorphism preserves the finite part of a splitting over a henselian pair.**
* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_of_isCompl`: the complement of an
  invariant open is invariant.
* `AlgebraicGeometry.DescentDatum.isCompl_opensRange_of_isIso_coprodDesc`: two open immersions
  exhibiting their common target as a binary coproduct have complementary open images.
* `AlgebraicGeometry.DescentDatum.exists_isCompl_isTransitionInvariant_of_henselianPair`: the
  scheme of a quasi-compact separated étale descent datum relative to a finite morphism onto a
  henselian pair splits into two complementary invariant opens, one finite over the base and one
  carrying no point over the closed fibre.
* `AlgebraicGeometry.DescentDatum.isColimitBinaryCofanRestrictOpenHom`: **a descent datum is the
  coproduct of its restrictions to two complementary invariant opens**, and
  `AlgebraicGeometry.DescentDatum.isColimitBinaryCofanEtaleRestrictOpen` and
  `AlgebraicGeometry.DescentDatum.isColimitBinaryCofanQcSepEtaleRestrictOpen` the same statement
  in `AlgebraicGeometry.EtaleDescentData` and in
  `AlgebraicGeometry.QuasiCompactSeparatedEtaleDescentData`.
* `AlgebraicGeometry.DescentDatum.prodOver_hom_ext`: **the base changes of two complementary
  opens of `V` are a jointly epimorphic pair out of `V ×_S X`**, with
  `AlgebraicGeometry.DescentDatum.over_hom_ext_of_isCompl` and
  `AlgebraicGeometry.DescentDatum.splitOverDesc` the corresponding statements for `V` itself.
* `AlgebraicGeometry.DescentDatum.etale_restrictOpen_over_hom`,
  `AlgebraicGeometry.DescentDatum.quasiCompact_restrictOpen_over_hom` and
  `AlgebraicGeometry.DescentDatum.isSeparated_restrictOpen_over_hom`: the restricted datum stays
  étale, quasi-compact and separated over `X`.

## References

* [Stacks Project, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.DescentDatum

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (W : D.over.left.Opens)

/-! ### An open of `V` base changed along `f` -/

/-- An open `W ⊆ V` base changed along `f` in the first factor: the open immersion
`W ×_S X ⟶ V ×_S X`. -/
abbrev opensSourceMap : pullback ((W.ι ≫ D.over.hom) ≫ f) f ⟶ pullback (D.over.hom ≫ f) f :=
  pullback.map ((W.ι ≫ D.over.hom) ≫ f) f (D.over.hom ≫ f) f W.ι (𝟙 X) (𝟙 S)
    (by simp) (by simp)

/-- An open `W ⊆ V` base changed along `f` in the second factor: the open immersion
`X ×_S W ⟶ X ×_S V`. -/
abbrev opensTargetMap : pullback f ((W.ι ≫ D.over.hom) ≫ f) ⟶ pullback f (D.over.hom ≫ f) :=
  pullback.map f ((W.ι ≫ D.over.hom) ≫ f) f (D.over.hom ≫ f) (𝟙 X) W.ι (𝟙 S)
    (by simp) (by simp)

/-- The image of `W ×_S X` in `V ×_S X` is the preimage of `W` under the first projection. -/
lemma range_opensSourceMap :
    Set.range (D.opensSourceMap W).base =
      ↑(pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W) := by
  rw [range_pullbackMapFst_of_isOpenImmersion W.ι (D.over.hom ≫ f) _ f
    (Category.assoc _ _ _) (by simp) (by simp)]
  simp

/-- The image of `X ×_S W` in `X ×_S V` is the preimage of `W` under the second projection. -/
lemma range_opensTargetMap :
    Set.range (D.opensTargetMap W).base =
      ↑(pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ W) := by
  rw [range_pullbackMapSnd_of_isOpenImmersion W.ι (D.over.hom ≫ f) _ f
    (Category.assoc _ _ _) (by simp) (by simp)]
  simp

/-- The open immersion `W ×_S X ⟶ V ×_S X` commutes with the second projections to `X`. -/
@[reassoc]
lemma opensSourceMap_comp_snd :
    D.opensSourceMap W ≫ pullback.snd (D.over.hom ≫ f) f =
      pullback.snd ((W.ι ≫ D.over.hom) ≫ f) f := by
  rw [pullback.lift_snd, Category.comp_id]

/-- The open immersion `X ×_S W ⟶ X ×_S V` followed by the second projection to `V` is the
second projection to `W` followed by the inclusion `W ⟶ V`. -/
@[reassoc]
lemma opensTargetMap_comp_snd :
    D.opensTargetMap W ≫ pullback.snd f (D.over.hom ≫ f) =
      pullback.snd f ((W.ι ≫ D.over.hom) ≫ f) ≫ W.ι := by
  rw [pullback.lift_snd]

/-! ### Two complementary opens, read as sets -/

variable {T : Scheme.{u}}

/-- Two complementary opens cover the space. -/
lemma union_coe_eq_univ_of_isCompl {U U' : T.Opens} (h : IsCompl U U') :
    (U : Set T) ∪ (U' : Set T) = Set.univ := by
  simpa using congrArg (fun V : T.Opens ↦ (V : Set T)) (codisjoint_iff.mp h.codisjoint)

/-- Two complementary opens are disjoint. -/
lemma inter_coe_eq_empty_of_isCompl {U U' : T.Opens} (h : IsCompl U U') :
    (U : Set T) ∩ (U' : Set T) = ∅ := by
  simpa using congrArg (fun V : T.Opens ↦ (V : Set T)) (disjoint_iff.mp h.disjoint)

/-- Complementarity of two opens, from complementarity of their underlying sets. -/
lemma isCompl_of_union_coe_of_inter_coe {U U' : T.Opens}
    (hu : (U : Set T) ∪ (U' : Set T) = Set.univ)
    (hi : (U : Set T) ∩ (U' : Set T) = ∅) : IsCompl U U' := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  exact ⟨TopologicalSpace.Opens.ext (by simpa using hi),
    TopologicalSpace.Opens.ext (by simpa using hu)⟩

/-- A point lies in one of two complementary opens. -/
private lemma mem_or_mem_of_isCompl {U U' : T.Opens} (h : IsCompl U U') (x : T) :
    x ∈ U ∨ x ∈ U' :=
  (union_coe_eq_univ_of_isCompl h).ge (Set.mem_univ x)

/-- A point cannot lie in two complementary opens. -/
private lemma false_of_mem_of_mem_of_isCompl {U U' : T.Opens} (h : IsCompl U U') {x : T}
    (hx : x ∈ U) (hx' : x ∈ U') : False :=
  (inter_coe_eq_empty_of_isCompl h).subset ⟨hx, hx'⟩

/-- The preimages of two complementary opens along a morphism are complementary. -/
lemma isCompl_preimage {Y : Scheme.{u}} (g : Y ⟶ T) {U U' : T.Opens} (h : IsCompl U U') :
    IsCompl (g ⁻¹ᵁ U) (g ⁻¹ᵁ U') := by
  refine isCompl_of_union_coe_of_inter_coe (Set.eq_univ_of_forall fun x ↦ ?_)
    (Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_)
  · exact mem_or_mem_of_isCompl h (g x)
  · exact false_of_mem_of_mem_of_isCompl h hx.1 hx.2

/-- Two open immersions whose images are complementary opens have complementary images. -/
lemma isCompl_opensRange_of_range {Y Y' : Scheme.{u}} (a : Y ⟶ T) (b : Y' ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] {U U' : T.Opens}
    (ha : Set.range a.base = (U : Set T)) (hb : Set.range b.base = (U' : Set T))
    (h : IsCompl U U') : IsCompl a.opensRange b.opensRange := by
  have ea : a.opensRange = U := TopologicalSpace.Opens.ext ha
  have eb : b.opensRange = U' := TopologicalSpace.Opens.ext hb
  rwa [ea, eb]

/-- **Two open immersions exhibiting their common target as a binary coproduct have
complementary open images.** -/
lemma isCompl_opensRange_of_isIso_coprodDesc {Y Y' : Scheme.{u}} (a : Y ⟶ T) (b : Y' ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsIso (coprod.desc a b)] :
    IsCompl a.opensRange b.opensRange := by
  refine isCompl_of_union_coe_of_inter_coe
    (Stacks.Etale.union_range_eq_univ_of_isIso_coprodDesc a b)
    (Set.eq_empty_iff_forall_notMem.mpr ?_)
  rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  refine inl_ne_inr Y Y' y z ((Scheme.homeoOfIso (asIso (coprod.desc a b))).injective ?_)
  show (coprod.desc a b) ((coprod.inl : Y ⟶ Y ⨿ Y') y) =
    (coprod.desc a b) ((coprod.inr : Y' ⟶ Y ⨿ Y') z)
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, coprod.inl_desc, coprod.inr_desc,
    hy, hz]

/-! ### The complement of an invariant open is invariant -/

/-- **The complement of an invariant open is invariant.** -/
theorem isTransitionInvariant_of_isCompl (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    (hW : D.IsTransitionInvariant W) : D.IsTransitionInvariant W' := by
  refine le_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · obtain ⟨z, hz, rfl⟩ := hy
    show pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom z) ∈ W'
    rcases mem_or_mem_of_isCompl hWW'
        (pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom z)) with h | h
    · refine absurd ?_ (false_of_mem_of_mem_of_isCompl hWW' · hz)
      have e := Scheme.hom_inv_apply D.transitionPullbackIso z
      have h₂ := D.mem_of_isTransitionInvariant' W hW _ h
      rwa [e] at h₂
    · exact h
  · have e := Scheme.inv_hom_apply D.transitionPullbackIso y
    refine ⟨D.transitionPullbackIso.inv y, ?_, e⟩
    show pullback.fst (D.over.hom ≫ f) f (D.transitionPullbackIso.inv y) ∈ W'
    rcases mem_or_mem_of_isCompl hWW'
        (pullback.fst (D.over.hom ≫ f) f (D.transitionPullbackIso.inv y)) with h | h
    · refine absurd ?_ (false_of_mem_of_mem_of_isCompl hWW' · hy)
      have h₂ := D.mem_of_isTransitionInvariant W hW _ h
      rwa [e] at h₂
    · exact h

/-! ### The gluing isomorphism preserves the finite part of a splitting -/

section Henselian

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of A)}

/-- **The gluing isomorphism of a descent datum preserves the finite part of a splitting over a
henselian pair.** Let `(V, φ)` be a descent datum relative to a finite morphism
`f : X ⟶ Spec A`, with `I ⊆ A` inside the Jacobson radical, and let `V = W ⊔ W'` be a splitting
of `V` into two complementary opens with `W` finite over `Spec A` and `W'` carrying no point
over `Spec (A ⧸ I)`. Then `W` is invariant under `φ`. -/
theorem isTransitionInvariant_of_isFinite_of_isEmpty_closedFiber
    (hI : I ≤ Ring.jacobson A) (hf : IsFinite f) (D : DescentDatum f)
    (W W' : D.over.left.Opens) (hWW' : IsCompl W W')
    (hfin : IsFinite ((W.ι ≫ D.over.hom) ≫ f))
    (hempty : IsEmpty (pullback ((W'.ι ≫ D.over.hom) ≫ f)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    D.IsTransitionInvariant W := by
  have := hf
  have := hfin
  have hjf : D.opensSourceMap W ≫ (pullback.snd (D.over.hom ≫ f) f ≫ f) =
      pullback.snd ((W.ι ≫ D.over.hom) ≫ f) f ≫ f := by
    rw [D.opensSourceMap_comp_snd_assoc]
  have hjfq : IsFinite (D.opensSourceMap W ≫ (pullback.snd (D.over.hom ≫ f) f ≫ f)) := by
    rw [hjf]; infer_instance
  have hcov' : Set.range (D.opensTargetMap W ≫ D.transitionPullbackIso.inv).base ∪
      Set.range (D.opensTargetMap W' ≫ D.transitionPullbackIso.inv).base = Set.univ := by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    have hback : ∀ (U : D.over.left.Opens),
        pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom y) ∈ U →
          y ∈ Set.range (D.opensTargetMap U ≫ D.transitionPullbackIso.inv).base := by
      intro U hU
      obtain ⟨t, ht⟩ : D.transitionPullbackIso.hom y ∈
          Set.range (D.opensTargetMap U).base := by
        rw [D.range_opensTargetMap U]; exact hU
      refine ⟨t, ?_⟩
      rw [Scheme.Hom.comp_base]
      show D.transitionPullbackIso.inv (D.opensTargetMap U t) = y
      rw [ht, Scheme.hom_inv_apply]
    rcases mem_or_mem_of_isCompl hWW'
        (pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom y)) with h | h
    · exact Or.inl (hback W h)
    · exact Or.inr (hback W' h)
  have haway : (D.opensTargetMap W' ≫ D.transitionPullbackIso.inv) ≫
        (pullback.snd (D.over.hom ≫ f) f ≫ f) =
      pullback.snd f ((W'.ι ≫ D.over.hom) ≫ f) ≫ ((W'.ι ≫ D.over.hom) ≫ f) := by
    simp only [Category.assoc]
    rw [← Category.assoc D.transitionPullbackIso.inv,
      D.transitionPullbackIso_inv_comp_pullbackSnd]
    simpa using congrArg (· ≫ D.over.hom ≫ f) (D.opensTargetMap_comp_snd W')
  have hfib' : IsEmpty (pullback ((D.opensTargetMap W' ≫ D.transitionPullbackIso.inv) ≫
        (pullback.snd (D.over.hom ≫ f) f ≫ f))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}) :=
    ⟨fun x ↦ hempty.elim (pullback.map
      ((D.opensTargetMap W' ≫ D.transitionPullbackIso.inv) ≫
        (pullback.snd (D.over.hom ≫ f) f ≫ f))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((W'.ι ≫ D.over.hom) ≫ f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (pullback.snd f ((W'.ι ≫ D.over.hom) ≫ f)) (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans haway) (by simp) x)⟩
  have hsub := Stacks.Etale.range_subset_range_of_isFinite hI
    (pullback.snd (D.over.hom ≫ f) f ≫ f) (D.opensSourceMap W)
    (D.opensTargetMap W ≫ D.transitionPullbackIso.inv)
    (D.opensTargetMap W' ≫ D.transitionPullbackIso.inv) hcov' hfib'
  refine D.isTransitionInvariant_of_le W fun y hy ↦ ?_
  obtain ⟨z, hz, rfl⟩ := hy
  have hzmem : z ∈ Set.range (D.opensSourceMap W).base := by
    rw [D.range_opensSourceMap W]; exact hz
  obtain ⟨t, ht⟩ := hsub hzmem
  have ht' : D.transitionPullbackIso.hom z = D.opensTargetMap W t := by
    rw [Scheme.Hom.comp_base] at ht
    change D.transitionPullbackIso.inv (D.opensTargetMap W t) = z at ht
    rw [← ht, Scheme.inv_hom_apply]
  show pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom z) ∈ W
  rw [ht']
  have : D.opensTargetMap W t ∈ Set.range (D.opensTargetMap W).base := ⟨t, rfl⟩
  rwa [D.range_opensTargetMap W] at this

/-! ### The splitting of Tag 0BTN, applied to the scheme of a descent datum -/

/-- A prime of `B` lies over the closed fibre `V(I)` of `Spec A` exactly when it contains
`IB`. -/
private lemma mem_zeroLocus_comap_iff {B : Type u} [CommRing B] (b : A →+* B)
    (w : PrimeSpectrum B) :
    PrimeSpectrum.comap b w ∈ PrimeSpectrum.zeroLocus (I : Set A) ↔
      w ∈ PrimeSpectrum.zeroLocus ((I.map b : Ideal B) : Set B) := by
  rw [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
  exact Iff.rfl

/-- A point of `Spec B` lies over the closed fibre of `Spec A` exactly when it lies in the
closed fibre of `Spec B`. -/
private lemma mem_range_specMap_quotientMk_comap_iff {B : Type u} [CommRing B] (b : A →+* B)
    (w : Spec (CommRingCat.of B)) :
    Spec.map (CommRingCat.ofHom b) w ∈
        Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ↔
      w ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map b)))) :=
  (Set.ext_iff.mp (range_spec_map_quotient_mk I) _).trans
    ((mem_zeroLocus_comap_iff b w).trans
      (Set.ext_iff.mp (range_spec_map_quotient_mk (I.map b)) w).symm)

/-- **The scheme of a quasi-compact separated étale descent datum relative to a finite morphism
onto a henselian pair splits into two complementary invariant opens**, one finite over the base
and one carrying no point over the closed fibre.

The affine scheme `X` is presented by an isomorphism `e : X ≅ Spec B` together with the equation
`he` naming the structure morphism, and the hypothesis `hclosed` is that the closed fibre of `V`
over `Spec (B ⧸ IB)` is finite. The two conclusions about the pieces are stated relative to the
base `Spec A`. -/
theorem exists_isCompl_isTransitionInvariant_of_henselianPair
    (hI : I ≤ Ring.jacobson A) (hf : IsFinite f) (D : DescentDatum f) (hD : Etale D.over.hom)
    (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom)
    {B : Type u} [CommRing B] (b : A →+* B) (hB : HenselianPair B (I.map b))
    (e : X ≅ Spec (CommRingCat.of B))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom b) = f)
    (hclosed : IsFinite (pullback.snd (D.over.hom ≫ e.hom)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map b)))))) :
    ∃ W W' : D.over.left.Opens, IsCompl W W' ∧
      D.IsTransitionInvariant W ∧ D.IsTransitionInvariant W' ∧
      IsFinite ((W.ι ≫ D.over.hom) ≫ f) ∧
      IsEmpty (pullback ((W'.ι ≫ D.over.hom) ≫ f)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}) := by
  have := hf
  have := hD
  have := hqc
  have := hsep
  have := hclosed
  have hbfin : IsFinite (Spec.map (CommRingCat.ofHom b)) := by
    rw [show Spec.map (CommRingCat.ofHom b) = e.inv ≫ f by rw [← he, Iso.inv_hom_id_assoc]]
    infer_instance
  obtain ⟨Vfin, Vaway, iFin, iAway, hiso, hfinB, hemptyB, hoFin, hoAway, -⟩ :=
    Stacks.Etale.exists_coprod_isOpenImmersion_isFinite_etale_and_isEmpty_closedFiber
      B (I.map b) hB D.over.left (D.over.hom ≫ e.hom)
  have := hoFin
  have := hoAway
  have hcompl : IsCompl iFin.opensRange iAway.opensRange :=
    isCompl_opensRange_of_isIso_coprodDesc iFin iAway
  have hcomp : (D.over.hom ≫ e.hom) ≫ Spec.map (CommRingCat.ofHom b) = D.over.hom ≫ f := by
    rw [Category.assoc, he]
  have hfinA : IsFinite ((iFin.opensRange.ι ≫ D.over.hom) ≫ f) := by
    have hfac : iFin.isoOpensRange.hom ≫ iFin.opensRange.ι ≫ (D.over.hom ≫ e.hom) =
        iFin ≫ (D.over.hom ≫ e.hom) := by
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    have hpiece : IsFinite (iFin.opensRange.ι ≫ (D.over.hom ≫ e.hom)) := by
      rw [show iFin.opensRange.ι ≫ (D.over.hom ≫ e.hom) =
          iFin.isoOpensRange.inv ≫ iFin ≫ (D.over.hom ≫ e.hom) by
        rw [← hfac, Iso.inv_hom_id_assoc]]
      have := hfinB
      infer_instance
    rw [show (iFin.opensRange.ι ≫ D.over.hom) ≫ f =
        (iFin.opensRange.ι ≫ (D.over.hom ≫ e.hom)) ≫ Spec.map (CommRingCat.ofHom b) by
      rw [Category.assoc, Category.assoc, hcomp]]
    infer_instance
  have hemptyA : IsEmpty (pullback ((iAway.opensRange.ι ≫ D.over.hom) ≫ f)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}) := by
    have hran : Set.range ((iAway.opensRange.ι ≫ D.over.hom) ≫ f) =
        Set.range (iAway ≫ ((D.over.hom ≫ e.hom) ≫ Spec.map (CommRingCat.ofHom b))) := by
      rw [hcomp, ← range_eq_range_of_surjective _ _ iAway.isoOpensRange.hom]
      · rw [← Category.assoc, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Category.assoc]
    have hdisjB := Scheme.isEmpty_pullback_iff.mp hemptyB
    rw [Set.disjoint_left] at hdisjB
    rw [Scheme.isEmpty_pullback_iff, hran, Set.disjoint_left]
    rintro p ⟨y₀, rfl⟩ hp
    refine hdisjB (Set.mem_range_self y₀) ?_
    rw [← mem_range_specMap_quotientMk_comap_iff (I := I) b]
    simp only [Scheme.Hom.comp_apply] at hp ⊢
    exact hp
  have hinvFin : D.IsTransitionInvariant iFin.opensRange :=
    D.isTransitionInvariant_of_isFinite_of_isEmpty_closedFiber hI hf iFin.opensRange
      iAway.opensRange hcompl hfinA hemptyA
  exact ⟨iFin.opensRange, iAway.opensRange, hcompl, hinvFin,
    D.isTransitionInvariant_of_isCompl iFin.opensRange iAway.opensRange hcompl hinvFin,
    hfinA, hemptyA⟩

end Henselian

/-! ### Two complementary invariant opens split the datum -/

/-- **`V` is the coproduct of two complementary opens.** -/
def isColimitBinaryCofanOpens (W' : D.over.left.Opens) (hWW' : IsCompl W W') :
    IsColimit (BinaryCofan.mk W.ι W'.ι) :=
  (nonempty_isColimit_binaryCofanMk_of_isCompl W.ι W'.ι
    (isCompl_opensRange_of_range W.ι W'.ι W.range_ι W'.range_ι hWW')).some

/-- **`V ×_S X` is the coproduct of the base changes of two complementary opens.** -/
def isColimitBinaryCofanOpensSourceMap (W' : D.over.left.Opens) (hWW' : IsCompl W W') :
    IsColimit (BinaryCofan.mk (D.opensSourceMap W) (D.opensSourceMap W')) :=
  (nonempty_isColimit_binaryCofanMk_of_isCompl _ _
    (isCompl_opensRange_of_range _ _ (D.range_opensSourceMap W) (D.range_opensSourceMap W')
      (isCompl_preimage (pullback.fst (D.over.hom ≫ f) f) hWW'))).some

/-- Morphisms out of `V ×_S X` read in the two coordinate systems: the `Over S`-product
`V ×_S X` of `AlgebraicGeometry.DescentData` and the literal fibre product. -/
lemma opensSourceMap_comp_left {Q : Over S}
    (γ : (Over.map f).obj D.over ⨯ Over.mk f ⟶ Q) :
    D.opensSourceMap W ≫
        (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫ γ.left =
      (Over.prodLeftIsoPullback ((Over.map f).obj (D.restrictOpenObj W)) (Over.mk f)).inv ≫
        (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ γ).left := by
  have hm : D.opensSourceMap W =
      (Over.prodLeftIsoPullback ((Over.map f).obj (D.restrictOpenObj W)) (Over.mk f)).inv ≫
        (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f))).left ≫
        (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom :=
    (DescentData.prodMap_left (D.restrictOpenιMap W) (𝟙 (Over.mk f))).symm
  calc D.opensSourceMap W ≫
        (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫ γ.left
      = ((Over.prodLeftIsoPullback ((Over.map f).obj (D.restrictOpenObj W)) (Over.mk f)).inv ≫
          (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f))).left ≫
          (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom) ≫
          (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫ γ.left := by
        rw [hm]
    _ = (Over.prodLeftIsoPullback ((Over.map f).obj (D.restrictOpenObj W)) (Over.mk f)).inv ≫
          (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f))).left ≫ γ.left := by
        simp
    _ = (Over.prodLeftIsoPullback ((Over.map f).obj (D.restrictOpenObj W)) (Over.mk f)).inv ≫
          (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ γ).left := by
        rw [Over.comp_left]

/-- **Two complementary opens of `V` base change to a jointly epimorphic pair of morphisms out
of `V ×_S X`.** Two morphisms of `S`-schemes out of `V ×_S X` which agree after restriction to
`W ×_S X` and to `W' ×_S X` are equal. -/
lemma prodOver_hom_ext (W' : D.over.left.Opens) (hWW' : IsCompl W W') {Q : Over S}
    {α β : (Over.map f).obj D.over ⨯ Over.mk f ⟶ Q}
    (h : prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ α =
      prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ β)
    (h' : prod.map (D.restrictOpenιMap W') (𝟙 (Over.mk f)) ≫ α =
      prod.map (D.restrictOpenιMap W') (𝟙 (Over.mk f)) ≫ β) :
    α = β :=
  Over.OverMorphism.ext
    ((cancel_epi (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv).mp
      (BinaryCofan.IsColimit.hom_ext (D.isColimitBinaryCofanOpensSourceMap W W' hWW')
        ((D.opensSourceMap_comp_left W α).trans
          ((congrArg (fun g ↦ (Over.prodLeftIsoPullback
              ((Over.map f).obj (D.restrictOpenObj W)) (Over.mk f)).inv ≫ Over.Hom.left g)
            h).trans (D.opensSourceMap_comp_left W β).symm))
        ((D.opensSourceMap_comp_left W' α).trans
          ((congrArg (fun g ↦ (Over.prodLeftIsoPullback
              ((Over.map f).obj (D.restrictOpenObj W')) (Over.mk f)).inv ≫ Over.Hom.left g)
            h').trans (D.opensSourceMap_comp_left W' β).symm))))

/-- **Two complementary opens of `V` are jointly epimorphic.** -/
lemma over_hom_ext_of_isCompl (W' : D.over.left.Opens) (hWW' : IsCompl W W') {Q : Over X}
    {α β : D.over ⟶ Q} (h : D.restrictOpenι W ≫ α = D.restrictOpenι W ≫ β)
    (h' : D.restrictOpenι W' ≫ α = D.restrictOpenι W' ≫ β) : α = β :=
  Over.OverMorphism.ext
    (BinaryCofan.IsColimit.hom_ext (D.isColimitBinaryCofanOpens W W' hWW')
      (congrArg Over.Hom.left h) (congrArg Over.Hom.left h'))

/-- The morphism out of `V` determined by its restrictions to two complementary opens, as a
morphism of schemes over `X`. -/
def splitOverDesc (W' : D.over.left.Opens) (hWW' : IsCompl W W') {Q : Over X}
    (u : D.restrictOpenObj W ⟶ Q) (u' : D.restrictOpenObj W' ⟶ Q) : D.over ⟶ Q :=
  Over.homMk (BinaryCofan.IsColimit.desc (D.isColimitBinaryCofanOpens W W' hWW') u.left u'.left)
    (BinaryCofan.IsColimit.hom_ext (D.isColimitBinaryCofanOpens W W' hWW')
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g ↦ g ≫ Q.hom)
          (BinaryCofan.IsColimit.inl_desc (D.isColimitBinaryCofanOpens W W' hWW')
            u.left u'.left)).trans (Over.w u)))
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g ↦ g ≫ Q.hom)
          (BinaryCofan.IsColimit.inr_desc (D.isColimitBinaryCofanOpens W W' hWW')
            u.left u'.left)).trans (Over.w u'))))

/-- The morphism `splitOverDesc W W' hWW' u u'` restricts to `u` on `W`. -/
@[simp]
lemma restrictOpenι_comp_splitOverDesc_left (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    {Q : Over X} (u : D.restrictOpenObj W ⟶ Q) (u' : D.restrictOpenObj W' ⟶ Q) :
    D.restrictOpenι W ≫ D.splitOverDesc W W' hWW' u u' = u :=
  Over.OverMorphism.ext
    (BinaryCofan.IsColimit.inl_desc (D.isColimitBinaryCofanOpens W W' hWW') u.left u'.left)

/-- The morphism `splitOverDesc W W' hWW' u u'` restricts to `u'` on `W'`. -/
@[simp]
lemma restrictOpenι_comp_splitOverDesc_right (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    {Q : Over X} (u : D.restrictOpenObj W ⟶ Q) (u' : D.restrictOpenObj W' ⟶ Q) :
    D.restrictOpenι W' ≫ D.splitOverDesc W W' hWW' u u' = u' :=
  Over.OverMorphism.ext
    (BinaryCofan.IsColimit.inr_desc (D.isColimitBinaryCofanOpens W W' hWW') u.left u'.left)

/-- **The compatibility square of a morphism of descent data out of `D` restricted to an
invariant open.** If the component `g` of the candidate morphism restricts along `W ⟶ V` to the
component of a morphism of descent data out of the restricted datum, then the compatibility
square of `g` holds after restriction to `W ×_S X`. -/
lemma prodMap_restrictOpenιMap_comm (hW : D.IsTransitionInvariant W) (E : DescentDatum f)
    (g : D.over ⟶ E.over) (v : D.restrictOpenObj W ⟶ E.over)
    (hv : D.restrictOpenι W ≫ g = v)
    (hcomm : prod.map ((Over.map f).map v) (𝟙 (Over.mk f)) ≫ E.transition.hom.left =
      (D.restrictOpen W hW).transition.hom.left ≫
        prod.map (𝟙 (Over.mk f)) ((Over.map f).map v)) :
    prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫
        (prod.map ((Over.map f).map g) (𝟙 (Over.mk f)) ≫ E.transition.hom.left) =
      prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫
        (D.transition.hom.left ≫ prod.map (𝟙 (Over.mk f)) ((Over.map f).map g)) := by
  have key : prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫
      prod.map ((Over.map f).map g) (𝟙 (Over.mk f)) =
      prod.map ((Over.map f).map v) (𝟙 (Over.mk f)) := by
    rw [prod.map_map, Category.comp_id, ← Functor.map_comp, hv]
  have key' : prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) ≫
      prod.map (𝟙 (Over.mk f)) ((Over.map f).map g) =
      prod.map (𝟙 (Over.mk f)) ((Over.map f).map v) := by
    rw [prod.map_map, Category.comp_id, ← Functor.map_comp, hv]
  have s₁ : prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫
        (prod.map ((Over.map f).map g) (𝟙 (Over.mk f)) ≫ E.transition.hom.left) =
      (D.restrictOpen W hW).transition.hom.left ≫
        prod.map (𝟙 (Over.mk f)) ((Over.map f).map v) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ E.transition.hom.left) key).trans hcomm)
  have s₂ : prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫
        (D.transition.hom.left ≫ prod.map (𝟙 (Over.mk f)) ((Over.map f).map g)) =
      (D.restrictOpen W hW).transition.hom.left ≫
        prod.map (𝟙 (Over.mk f)) ((Over.map f).map v) :=
    (Category.assoc _ _ _).symm.trans
      (((congrArg (fun k ↦ k ≫ prod.map (𝟙 (Over.mk f)) ((Over.map f).map g))
            (D.restrictOpen_transition_hom_left W hW).symm).trans
          (Category.assoc _ _ _)).trans
        (congrArg (fun k ↦ (D.restrictOpen W hW).transition.hom.left ≫ k) key'))
  exact s₁.trans s₂.symm

/-- **A descent datum splits along a splitting of its scheme into two complementary invariant
opens.** The two restricted data `(W, φ|_{W ×_S X})` and `(W', φ|_{W' ×_S X})` exhibit `(V, φ)`
as their coproduct in the category of descent data relative to `f`. -/
def isColimitBinaryCofanRestrictOpenHom (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    (hW : D.IsTransitionInvariant W) (hW' : D.IsTransitionInvariant W') :
    IsColimit (BinaryCofan.mk (D.restrictOpenHom W hW) (D.restrictOpenHom W' hW')) :=
  BinaryCofan.isColimitMk
    (fun s ↦
      { hom := fun _ ↦ D.splitOverDesc W W' hWW' (s.inl.hom ()) (s.inr.hom ())
        comm := fun _ _ ↦ D.prodOver_hom_ext W W' hWW'
          (D.prodMap_restrictOpenιMap_comm W hW s.pt _ (s.inl.hom ())
            (D.restrictOpenι_comp_splitOverDesc_left W W' hWW' _ _) (s.inl.comm () ()))
          (D.prodMap_restrictOpenιMap_comm W' (D.isTransitionInvariant_of_isCompl W W' hWW' hW)
            s.pt _ (s.inr.hom ())
            (D.restrictOpenι_comp_splitOverDesc_right W W' hWW' _ _) (s.inr.comm () ())) })
    (fun s ↦ DescentData.hom_ext fun _ ↦
      D.restrictOpenι_comp_splitOverDesc_left W W' hWW' (s.inl.hom ()) (s.inr.hom ()))
    (fun s ↦ DescentData.hom_ext fun _ ↦
      D.restrictOpenι_comp_splitOverDesc_right W W' hWW' (s.inl.hom ()) (s.inr.hom ()))
    (fun _ _ h₁ h₂ ↦ DescentData.hom_ext fun _ ↦
      D.over_hom_ext_of_isCompl W W' hWW'
        ((congrArg (fun k ↦ k.hom ()) h₁).trans
          (D.restrictOpenι_comp_splitOverDesc_left W W' hWW' _ _).symm)
        ((congrArg (fun k ↦ k.hom ()) h₂).trans
          (D.restrictOpenι_comp_splitOverDesc_right W W' hWW' _ _).symm))

/-! ### The two pieces in the étale, quasi-compact and separated subcategories -/

/-- The restriction of an étale descent datum to an invariant open is étale over `X`. -/
lemma etale_restrictOpen_over_hom (hW : D.IsTransitionInvariant W) [Etale D.over.hom] :
    Etale (D.restrictOpen W hW).over.hom := by
  show Etale (W.ι ≫ D.over.hom)
  infer_instance

/-- The restriction of a separated descent datum to an invariant open is separated over `X`. -/
lemma isSeparated_restrictOpen_over_hom (hW : D.IsTransitionInvariant W)
    [IsSeparated D.over.hom] : IsSeparated (D.restrictOpen W hW).over.hom := by
  show IsSeparated (W.ι ≫ D.over.hom)
  infer_instance

/-- The restriction of a quasi-compact descent datum to an invariant open with open complement
is quasi-compact over `X`. -/
lemma quasiCompact_restrictOpen_over_hom (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    (hW : D.IsTransitionInvariant W) [QuasiCompact D.over.hom] :
    QuasiCompact (D.restrictOpen W hW).over.hom := by
  have hset : (W : Set D.over.left) = ((W' : Set D.over.left))ᶜ := by
    exact Set.ext fun x ↦ ⟨fun hx hx' ↦ false_of_mem_of_mem_of_isCompl hWW' hx hx',
      fun hx ↦ (mem_or_mem_of_isCompl hWW' x).resolve_right hx⟩
  have hclosed : IsClosedImmersion W.ι := by
    refine IsClosedImmersion.of_isPreimmersion W.ι ?_
    rw [Scheme.Opens.range_ι, hset]
    exact W'.isOpen.isClosed_compl
  show QuasiCompact (W.ι ≫ D.over.hom)
  infer_instance

/-- An étale descent datum, as an object of `AlgebraicGeometry.EtaleDescentData`. -/
abbrev toEtaleDescentData [Etale D.over.hom] : EtaleDescentData f := ⟨D, inferInstance⟩

/-- The restriction of an étale descent datum to an invariant open, as an object of
`AlgebraicGeometry.EtaleDescentData`. -/
abbrev etaleRestrictOpen (hW : D.IsTransitionInvariant W) [Etale D.over.hom] :
    EtaleDescentData f :=
  ⟨D.restrictOpen W hW, D.etale_restrictOpen_over_hom W hW⟩

/-- **The splitting of an étale descent datum along two complementary invariant opens, in the
category of étale descent data relative to `f`.** -/
def isColimitBinaryCofanEtaleRestrictOpen (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    (hW : D.IsTransitionInvariant W) (hW' : D.IsTransitionInvariant W') [Etale D.over.hom] :
    IsColimit (BinaryCofan.mk
      (ObjectProperty.homMk (D.restrictOpenHom W hW) :
        D.etaleRestrictOpen W hW ⟶ D.toEtaleDescentData)
      (ObjectProperty.homMk (D.restrictOpenHom W' hW') :
        D.etaleRestrictOpen W' hW' ⟶ D.toEtaleDescentData)) :=
  isColimitOfReflectsOfMapIsColimit (ObjectProperty.ι (IsEtaleDescentData f)) _ _
    (D.isColimitBinaryCofanRestrictOpenHom W W' hWW' hW hW')

/-- A quasi-compact separated étale descent datum, as an object of
`AlgebraicGeometry.QuasiCompactSeparatedEtaleDescentData`. -/
abbrev toQcSepEtaleDescentData [Etale D.over.hom] [QuasiCompact D.over.hom]
    [IsSeparated D.over.hom] : QuasiCompactSeparatedEtaleDescentData f :=
  ⟨D.toEtaleDescentData, inferInstance, inferInstance⟩

/-- The restriction of a quasi-compact separated étale descent datum to an invariant open with
open complement, as an object of
`AlgebraicGeometry.QuasiCompactSeparatedEtaleDescentData`. -/
abbrev qcSepEtaleRestrictOpen (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    (hW : D.IsTransitionInvariant W) [Etale D.over.hom] [QuasiCompact D.over.hom]
    [IsSeparated D.over.hom] : QuasiCompactSeparatedEtaleDescentData f :=
  ⟨D.etaleRestrictOpen W hW, D.quasiCompact_restrictOpen_over_hom W W' hWW' hW,
    D.isSeparated_restrictOpen_over_hom W hW⟩

/-- **The splitting of a quasi-compact separated étale descent datum along two complementary
invariant opens, in the category of quasi-compact separated étale descent data relative to
`f`.** -/
def isColimitBinaryCofanQcSepEtaleRestrictOpen (W' : D.over.left.Opens) (hWW' : IsCompl W W')
    (hW : D.IsTransitionInvariant W) (hW' : D.IsTransitionInvariant W') [Etale D.over.hom]
    [QuasiCompact D.over.hom] [IsSeparated D.over.hom] :
    IsColimit (BinaryCofan.mk
      (ObjectProperty.homMk (ObjectProperty.homMk (D.restrictOpenHom W hW)) :
        D.qcSepEtaleRestrictOpen W W' hWW' hW ⟶ D.toQcSepEtaleDescentData)
      (ObjectProperty.homMk (ObjectProperty.homMk (D.restrictOpenHom W' hW')) :
        D.qcSepEtaleRestrictOpen W' W hWW'.symm hW' ⟶ D.toQcSepEtaleDescentData)) :=
  isColimitOfReflectsOfMapIsColimit
    (ObjectProperty.ι (IsQuasiCompactSeparatedEtaleDescentData f)) _ _
    (D.isColimitBinaryCofanEtaleRestrictOpen W W' hWW' hW hW')

end AlgebraicGeometry.DescentDatum

end
