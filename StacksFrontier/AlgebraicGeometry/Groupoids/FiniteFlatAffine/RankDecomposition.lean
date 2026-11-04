module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree

/-!
# The rank decomposition of a groupoid scheme with finite locally free source

If the source map of a groupoid scheme is finite locally free, its object scheme is the
disjoint union of invariant open subschemes on which the source map has constant rank. On the
restricted groupoid attached to the piece of rank `r`, both the source and the target map are
finite locally free of rank `r`, and the piece of rank zero is empty.

The pieces are those of the degree decomposition of the source map; what has to be proved is
that they are invariant. An arrow whose source lies in the piece of rank `r` and whose target
lies in the piece of rank `d` forces `r = d`, because both ranks are the rank of one and the
same morphism to the spectrum of the residue field of that arrow.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_disjoint_invariant_rank_decomposition`: the
  decomposition into invariant rank strata.
* `AlgebraicGeometry.GroupoidScheme.restriction_arrows_iso_source_open`: the arrow scheme of
  the restriction to an invariant open is the fibre product of the source map with that open.
  This is how the restriction to an invariant affine open is seen to be an affine groupoid.

## Implementation notes

The family is indexed by all natural numbers, with the rank-zero member empty. Pairwise
disjointness together with the supremum being the whole object scheme expresses the disjoint
union; each member is then closed as well as open. The restricted groupoid is the canonical
restriction `AlgebraicGeometry.GroupoidScheme.restrict` along the open immersion of the piece.

The degree decomposition of
`Stacks.Morphisms.exists_isClopenDecomposition_isFiniteLocallyFreeOfRank` is stated for
`AlgebraicGeometry.Scheme.Hom.morphismRestrict`; it is transported here to the chosen fibre
product, which is the shape in which the arrow scheme of the restricted groupoid appears.

## References

* [Stacks Project, Tag 03BI](https://stacks.math.columbia.edu/tag/03BI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open TopologicalSpace
open scoped Function nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### Ranks over the spectrum of a field -/

/-- A finite locally free module of rank `r` is finite. -/
private theorem module_finite_of_isFiniteLocallyFreeOfRank {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank R M r) :
    Module.Finite R M := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  refine Module.Finite.of_localizationSpan (Set.range f) hspan ?_
  rintro ⟨g, ⟨i, rfl⟩⟩
  exact Module.Finite.of_basis (Classical.choice (hbasis i))

/-- Over a field, a finite locally free module of rank `r` has dimension `r`. -/
theorem finrank_eq_of_isFiniteLocallyFreeOfRank {K M : Type u} [Field K]
    [AddCommGroup M] [Module K M] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank K M r) :
    Module.finrank K M = r := by
  classical
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  have hnonzero : ∃ i, f i ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : Ideal.span (Set.range f) = (⊥ : Ideal K) :=
      Ideal.span_eq_bot.mpr (by rintro x ⟨i, rfl⟩; exact hn i)
    exact (show (⊤ : Ideal K) ≠ ⊥ from top_ne_bot) (hspan.symm.trans hz)
  obtain ⟨i, hi⟩ := hnonzero
  have hp : Submonoid.powers (f i) ≤ K⁰ := by
    intro x hx
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff x (f i)).mp hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (hj ▸ pow_ne_zero j hi)
  have : Nontrivial (Localization.Away (f i)) :=
    (IsLocalization.injective (Localization.Away (f i)) hp).nontrivial
  obtain ⟨b⟩ := hbasis i
  have h₁ : Module.finrank (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M) = r := by
    simpa using Module.finrank_eq_card_basis b
  have h₂ : Module.finrank K (LocalizedModule (Submonoid.powers (f i)) M) =
      Module.finrank K M :=
    IsLocalizedModule.finrank_eq (Submonoid.powers (f i)) (LocalizedModule.mkLinearMap _ M) hp
  have h₃ : Module.finrank (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M) =
      Module.finrank K (LocalizedModule (Submonoid.powers (f i)) M) :=
    IsLocalization.finrank_eq (Localization.Away (f i)) (Submonoid.powers (f i)) hp
  exact h₂.symm.trans (h₃.symm.trans h₁)

/-- For a finite locally free morphism of rank `d` to the spectrum of a ring, the global
sections of the source are a finite locally free module of rank `d`. -/
@[sga "1 I 4.10" "over Spec R"]
private theorem module_isFiniteLocallyFreeOfRank_of_specTarget {R : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec R) (d : ℕ) [IsFiniteLocallyFreeOfRank f d] :
    letI := ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom.toAlgebra
    Module.IsFiniteLocallyFreeOfRank ↑R ↑Γ(X, ⊤) d :=
  (sheafOfModules_isFiniteLocallyFreeOfRank_iff_module f d).mp inferInstance

/-- A morphism to the spectrum of a field has at most one rank. -/
private theorem rank_eq_of_specField {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) {r d : ℕ} [IsFiniteLocallyFreeOfRank f r]
    [IsFiniteLocallyFreeOfRank f d] : r = d := by
  let : Algebra K Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hr := module_isFiniteLocallyFreeOfRank_of_specTarget f r
  have hd := module_isFiniteLocallyFreeOfRank_of_specTarget f d
  exact (finrank_eq_of_isFiniteLocallyFreeOfRank hr).symm.trans
    (finrank_eq_of_isFiniteLocallyFreeOfRank hd)

/-- A morphism to the spectrum of a field which is finite locally free of rank zero admits no
section. -/
private theorem false_of_rank_zero_of_hom {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsFiniteLocallyFreeOfRank f 0]
    (x : Spec (CommRingCat.of K) ⟶ X) : False := by
  let : Algebra K Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hm : Module.IsFiniteLocallyFreeOfRank K Γ(X, ⊤) 0 :=
    module_isFiniteLocallyFreeOfRank_of_specTarget f 0
  have : Module.Finite K Γ(X, ⊤) := module_finite_of_isFiniteLocallyFreeOfRank hm
  have hdim : Module.finrank K Γ(X, ⊤) = 0 := finrank_eq_of_isFiniteLocallyFreeOfRank hm
  have : Subsingleton Γ(X, ⊤) := Module.finrank_zero_iff.mp hdim
  let φ : Γ(X, ⊤) →+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp x.appTop.hom
  exact zero_ne_one ((map_zero φ).symm.trans ((congrArg φ (Subsingleton.elim 0 1)).trans
    (map_one φ)))

/-! ### Transport of the rank along isomorphisms -/

/-- Precomposing with an isomorphism preserves the rank. -/
private theorem rank_of_source_iso {X Y S : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ S) (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] : IsFiniteLocallyFreeOfRank (e.hom ≫ f) r :=
  have hsq : IsPullback e.hom (e.hom ≫ f) f (𝟙 S) := IsPullback.of_horiz_isIso ⟨by simp⟩
  IsFiniteLocallyFreeOfRank.of_isPullback hsq

/-- Postcomposing with an isomorphism preserves the rank. -/
private theorem rank_post_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] : IsFiniteLocallyFreeOfRank (f ≫ e.hom) r :=
  IsFiniteLocallyFreeOfRank.of_isPullback
    (IsPullback.of_horiz_isIso (show CommSq (𝟙 X) (f ≫ e.hom) f e.inv from ⟨by simp⟩))

/-- The degree decomposition, read on the chosen fibre product instead of the restriction. -/
private theorem rank_pullbackSnd_of_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) (d : ℕ) (h : IsFiniteLocallyFreeOfRank (f ∣_ U) d) :
    IsFiniteLocallyFreeOfRank (pullback.snd f U.ι) d := by
  have : IsFiniteLocallyFreeOfRank (f ∣_ U) d := h
  have hsq := (isPullback_morphismRestrict f U).flip
  have hcomm : hsq.isoPullback.inv ≫ (f ∣_ U) = pullback.snd f U.ι ≫ 𝟙 U.toScheme := by
    rw [Category.comp_id, Iso.inv_comp_eq, hsq.isoPullback_hom_snd]
  exact IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_horiz_isIso ⟨hcomm⟩)

/-! ### Residue points and the empty rank-zero stratum -/

/-- The point of an open subscheme determined by a point of the source whose image lies in
it. -/
private def liftResiduePointToOpen {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) (U : X.Opens)
    (hy : f y ∈ U) : Spec (Y.residueField y) ⟶ U.toScheme := by
  refine IsOpenImmersion.lift U.ι (Y.fromSpecResidueField y ≫ f) ?_
  rintro x ⟨x', rfl⟩
  exact ⟨⟨f y, hy⟩, by simp [Scheme.fromSpecResidueField_apply]⟩

private theorem liftResiduePointToOpen_fac {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) (U : X.Opens)
    (hy : f y ∈ U) :
    liftResiduePointToOpen f y U hy ≫ U.ι = Y.fromSpecResidueField y ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

/-- An open on which the source map of a groupoid scheme has rank zero is empty, because the
identity section provides a point over every point of it. -/
private theorem source_rank_zero_open_eq_bot {S : Scheme.{u}} (G : GroupoidScheme S)
    (U : G.objects.left.Opens)
    (h : IsFiniteLocallyFreeOfRank (pullback.snd G.source.left U.ι) 0) : U = ⊥ := by
  refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => absurd hx (by simp)⟩
  let K := G.objects.left.residueField x
  let Z := Spec (CommRingCat.of K)
  let v : Z ⟶ U.toScheme := liftResiduePointToOpen (𝟙 G.objects.left) x U (by simpa using hx)
  let p := pullback.snd G.source.left U.ι
  let sec : U.toScheme ⟶ pullback G.source.left U.ι :=
    pullback.lift (U.ι ≫ G.identity.left) (𝟙 U.toScheme) (by
      have hunit : G.identity.left ≫ G.source.left = 𝟙 G.objects.left :=
        congrArg Over.Hom.left G.source_identity
      simp [Category.assoc, hunit])
  have hsec : sec ≫ p = 𝟙 U.toScheme := pullback.lift_snd _ _ _
  let q := pullback.snd p v
  let sec' : Z ⟶ pullback p v :=
    pullback.lift (v ≫ sec) (𝟙 Z)
      (by rw [Category.assoc, hsec, Category.comp_id, Category.id_comp])
  have : IsFiniteLocallyFreeOfRank p 0 := h
  have : IsFiniteLocallyFreeOfRank q 0 :=
    IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_hasPullback p v)
  exact (false_of_rank_zero_of_hom q sec').elim

/-! ### Invariance of the rank strata -/

/-- The inverse exchanges the fibre products of the source and of the target with an open of
the object scheme. -/
private def targetSourceOpenIso {S : Scheme.{u}} (G : GroupoidScheme S)
    (U : G.objects.left.Opens) :
    pullback G.target.left U.ι ≅ pullback G.source.left U.ι := by
  have : IsIso G.inverse.left := groupoidInverse_left_isIso G
  have hsource : G.inverse.left ≫ G.source.left = G.target.left :=
    congrArg Over.Hom.left G.source_inverse
  exact asIso (pullback.map G.target.left U.ι G.source.left U.ι G.inverse.left (𝟙 _) (𝟙 _)
    (by simpa using hsource.symm) (by simp))

private theorem targetSourceOpenIso_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    (U : G.objects.left.Opens) :
    (targetSourceOpenIso G U).hom ≫ pullback.snd G.source.left U.ι =
      pullback.snd G.target.left U.ι := by
  show pullback.lift (pullback.fst G.target.left U.ι ≫ G.inverse.left)
    (pullback.snd G.target.left U.ι) _ ≫ pullback.snd G.source.left U.ι = _
  exact pullback.lift_snd _ _ _

/-- For an invariant open `U`, the arrow scheme of the restricted groupoid is the fibre product
of the source map with `U`, compatibly with the source maps.

This is what makes the restriction of a groupoid to an invariant *affine* open an affine
groupoid: the source map of a finite locally free groupoid is an affine morphism, so the fibre
product is affine, and the isomorphism transports that to the restricted arrow scheme. -/
theorem restriction_arrows_iso_source_open {S : Scheme.{u}} (G : GroupoidScheme S)
    (U : G.objects.left.Opens) (hInv : IsInvariantOpen G U)
    (g : Over.mk (U.ι ≫ G.objects.hom) ⟶ G.objects) (hg : g.left = U.ι) :
    ∃ e : (restrictionArrows G g).left ≅ pullback G.source.left U.ι,
      e.hom ≫ pullback.snd G.source.left U.ι = (restrictionSource G g).left := by
  have hpre : G.source.left ⁻¹ᵁ U = G.target.left ⁻¹ᵁ U := by
    ext z
    refine ⟨hInv z, fun hz => ?_⟩
    have hs : G.source.left (G.inverse.left z) = G.target.left z := by
      have h : G.inverse.left ≫ G.source.left = G.target.left := by
        simpa only [Over.comp_left] using congrArg Over.Hom.left G.source_inverse
      exact congrArg (fun f : G.arrows.left ⟶ G.objects.left => f z) h
    have ht : G.target.left (G.inverse.left z) = G.source.left z := by
      have h : G.inverse.left ≫ G.target.left = G.source.left := by
        simpa only [Over.comp_left] using congrArg Over.Hom.left G.target_inverse
      exact congrArg (fun f : G.arrows.left ⟶ G.objects.left => f z) h
    have hsi : G.source.left (G.inverse.left z) ∈ U := by simpa [hs] using hz
    simpa [ht] using hInv (G.inverse.left z) hsi
  let tpre := pullback.snd g G.target
  let spre := pullback.fst G.source g
  let htp := (overFibreProduct_isPullback g G.target).isoPullback
  let hsp := (overFibreProduct_isPullback G.source g).isoPullback
  let canT := pullback.snd g.left G.target.left
  let canS := pullback.fst G.source.left g.left
  have : IsOpenImmersion g.left := by rw [hg]; infer_instance
  have : IsOpenImmersion canT := inferInstance
  have : IsOpenImmersion canS := inferInstance
  have hgRange : g.left.opensRange = U := by simp only [hg, Scheme.Opens.opensRange_ι]
  let arr := (restrictionArrowsToArrows G g).left
  have htp' : htp.hom ≫ canT = tpre.left :=
    (overFibreProduct_isPullback g G.target).isoPullback_hom_snd
  have hsp' : hsp.hom ≫ canS = spre.left :=
    (overFibreProduct_isPullback G.source g).isoPullback_hom_fst
  let hpa := (overFibreProduct_isPullback tpre spre).isoPullback
  let m := pullback.map tpre.left spre.left canT canS htp.hom hsp.hom (𝟙 G.arrows.left)
    (by simpa using htp'.symm) (by simpa using hsp'.symm)
  let ePB := hpa ≪≫ asIso m
  let canonicalArr := pullback.fst canT canS ≫ canT
  have hpaFst : hpa.hom ≫ pullback.fst tpre.left spre.left =
      (pullback.fst tpre spre).left :=
    (overFibreProduct_isPullback tpre spre).isoPullback_hom_fst
  have hmFst : m ≫ pullback.fst canT canS = pullback.fst tpre.left spre.left ≫ htp.hom := by
    dsimp only [m, pullback.map]
    simp only [pullback.lift_fst]
  have harrMid : ePB.hom ≫ canonicalArr = (pullback.fst tpre spre).left ≫ tpre.left := by
    calc
      ePB.hom ≫ canonicalArr = hpa.hom ≫ m ≫ pullback.fst canT canS ≫ canT := by
        simp [ePB, canonicalArr, Category.assoc]
      _ = hpa.hom ≫ (m ≫ pullback.fst canT canS) ≫ canT := by simp [Category.assoc]
      _ = hpa.hom ≫ (pullback.fst tpre.left spre.left ≫ htp.hom) ≫ canT := by rw [hmFst]
      _ = (hpa.hom ≫ pullback.fst tpre.left spre.left) ≫ htp.hom ≫ canT := by
        simp [Category.assoc]
      _ = (pullback.fst tpre spre).left ≫ tpre.left := by rw [hpaFst, htp']
  have harrEnd : (pullback.fst tpre spre).left ≫ tpre.left = arr := by
    show (pullback.fst tpre spre).left ≫ tpre.left =
      (pullback.fst tpre spre ≫ pullback.snd g G.target).left
    rw [Over.comp_left]
  have harrFac : ePB.hom ≫ canonicalArr = arr := harrMid.trans harrEnd
  have htrangeCan : Set.range canT = G.target.left ⁻¹ᵁ U := by
    show Set.range (pullback.snd g.left G.target.left) = G.target.left ⁻¹ᵁ U
    rw [IsOpenImmersion.range_pullbackSnd, hgRange]
  have hsrangeCan : Set.range canS = G.source.left ⁻¹ᵁ U := by
    show Set.range (pullback.fst G.source.left g.left) = G.source.left ⁻¹ᵁ U
    rw [IsOpenImmersion.range_pullbackFst]
    simp only [hgRange]
  have hrange : Set.range arr = Set.range (pullback.fst G.source.left U.ι) := by
    calc
      Set.range arr = Set.range canonicalArr := by
        rw [← harrFac]
        show Set.range (canonicalArr ∘ ePB.hom) = Set.range canonicalArr
        exact ePB.hom.surjective.range_comp canonicalArr
      _ = Set.range canT ∩ Set.range canS :=
        IsOpenImmersion.range_pullback_to_base_of_left canT canS
      _ = Set.range (pullback.fst G.source.left U.ι) := by
        rw [htrangeCan, hsrangeCan, ← hpre, Set.inter_self]
        simpa only [Scheme.Opens.opensRange_ι] using
          (IsOpenImmersion.range_pullbackFst U.ι G.source.left).symm
  have harrOpen : IsOpenImmersion arr := by
    have : IsOpenImmersion canonicalArr := inferInstance
    have : IsIso ePB.hom := inferInstance
    have h : IsOpenImmersion (ePB.hom ≫ canonicalArr) := inferInstance
    rwa [harrFac] at h
  let eFinal := IsOpenImmersion.isoOfRangeEq arr (pullback.fst G.source.left U.ι) hrange
  have hfinalFac : eFinal.hom ≫ pullback.fst G.source.left U.ι = arr := by
    simp [eFinal, IsOpenImmersion.isoOfRangeEq_hom_fac arr _ hrange]
  have hcomp₁ : eFinal.hom ≫ pullback.snd G.source.left U.ι ≫ U.ι = arr ≫ G.source.left := by
    rw [← hfinalFac, Category.assoc, pullback.condition]
  have hcomp₂ : (restrictionSource G g).left ≫ U.ι = arr ≫ G.source.left := by
    have hcond : restrictionSource G g ≫ g = restrictionArrowsToArrows G g ≫ G.source := by
      unfold restrictionSource restrictionArrowsToArrows restrictionArrows
      simp only [Category.assoc]
      rw [← pullback.condition, ← pullback.condition_assoc]
    simpa only [Over.comp_left, hg, arr] using congrArg Over.Hom.left hcond
  exact ⟨eFinal, (cancel_mono U.ι).1 (hcomp₁.trans hcomp₂.symm)⟩

/-- If a base change of `f` along `U.ι` has rank `r` and a map `c` is a base change of `f`
through a map into `U`, then `c` has rank `r`. -/
private theorem rank_of_isPullback_open {A X Z C : Scheme.{u}} (f : A ⟶ X) (U : X.Opens)
    (u : Z ⟶ U.toScheme) (q : C ⟶ A) (c : C ⟶ Z) (r : ℕ) {t : Z ⟶ X} (h : IsPullback q c f t)
    (hu : u ≫ U.ι = t) [IsFiniteLocallyFreeOfRank (pullback.snd f U.ι) r] :
    IsFiniteLocallyFreeOfRank c r := by
  subst hu
  let l := pullback.lift q (c ≫ u) (h.w.trans (Category.assoc _ _ _).symm)
  have htop : l ≫ pullback.fst f U.ι = q := pullback.lift_fst _ _ _
  have houter : IsPullback (l ≫ pullback.fst f U.ι) c f (u ≫ U.ι) := by rwa [htop]
  exact IsFiniteLocallyFreeOfRank.of_isPullback
    (houter.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f U.ι))

/-- An arrow whose source lies in the rank-`r` stratum and whose target lies in the rank-`d`
stratum forces `r = d`. -/
private theorem rank_eq_of_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    (U : ℕ → G.objects.left.Opens)
    (hsource : ∀ r, IsFiniteLocallyFreeOfRank (pullback.snd G.source.left (U r).ι) r)
    {r d : ℕ} (z : G.arrows.left) (hzs : G.source.left z ∈ U r)
    (hzt : G.target.left z ∈ U d) : r = d := by
  let K := G.arrows.left.residueField z
  let Z := Spec (CommRingCat.of K)
  let a : Z ⟶ G.arrows.left := G.arrows.left.fromSpecResidueField z
  let u : Z ⟶ (U r).toScheme := liftResiduePointToOpen G.source.left z (U r) hzs
  let v : Z ⟶ (U d).toScheme := liftResiduePointToOpen G.target.left z (U d) hzt
  have hu : u ≫ (U r).ι = a ≫ G.source.left :=
    liftResiduePointToOpen_fac G.source.left z (U r) hzs
  have hv : v ≫ (U d).ι = a ≫ G.target.left :=
    liftResiduePointToOpen_fac G.target.left z (U d) hzt
  let C := pullback G.comp.left a
  let c : C ⟶ Z := pullback.snd G.comp.left a
  have htargetRank : IsFiniteLocallyFreeOfRank (pullback.snd G.target.left (U d).ι) d := by
    have : IsFiniteLocallyFreeOfRank (pullback.snd G.source.left (U d).ι) d := hsource d
    have h := rank_of_source_iso (targetSourceOpenIso G (U d))
      (pullback.snd G.source.left (U d).ι) d
    rwa [targetSourceOpenIso_snd] at h
  let q₁ : C ⟶ G.arrows.left :=
    pullback.fst G.comp.left a ≫ (pullback.snd G.source G.target).left
  let q₂ : C ⟶ G.arrows.left :=
    pullback.fst G.comp.left a ≫ (pullback.fst G.source G.target).left
  have hcommon₁ : IsPullback q₁ c G.source.left (a ≫ G.source.left) := by
    simpa [q₁, C, Category.assoc] using (IsPullback.of_hasPullback G.comp.left a).paste_horiz
      ((GroupoidScheme.comp_source_isPullback G).map (Over.forget S)).flip
  have hcommon₂ : IsPullback q₂ c G.target.left (a ≫ G.target.left) := by
    simpa [q₂, C, Category.assoc] using (IsPullback.of_hasPullback G.comp.left a).paste_horiz
      ((GroupoidScheme.target_comp_isPullback G).map (Over.forget S))
  have h₁ : IsFiniteLocallyFreeOfRank c r :=
    have := hsource r
    rank_of_isPullback_open G.source.left (U r) u q₁ c r hcommon₁ hu
  have h₂ : IsFiniteLocallyFreeOfRank c d :=
    have := htargetRank
    rank_of_isPullback_open G.target.left (U d) v q₂ c d hcommon₂ hv
  exact rank_eq_of_specField c

/-! ### The decomposition -/

/-- **Stacks Project, Tag 03BI.** A groupoid scheme whose source map is finite locally free
decomposes by the rank into invariant opens. On each restricted groupoid, both the source and
the target map are finite locally free of that rank, and the rank-zero piece is empty. -/
@[stacks 03BI]
theorem exists_disjoint_invariant_rank_decomposition {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] :
    ∃ U : ℕ → G.objects.left.Opens,
      U 0 = ⊥ ∧
      (∀ r, IsClosed (U r : Set G.objects.left)) ∧
      Pairwise (Disjoint on U) ∧
      (⨆ r, U r) = ⊤ ∧
      ∀ r, IsInvariantOpen G (U r) ∧
        let g : Over.mk ((U r).ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk (U r).ι
        let H := GroupoidScheme.restrict G g
        IsFiniteLocallyFreeOfRank H.groupoid.source.left r ∧
          IsFiniteLocallyFreeOfRank H.groupoid.target.left r := by
  classical
  obtain ⟨U, hdec, hRestrict⟩ :=
    exists_isClopenDecomposition_isFiniteLocallyFreeOfRank G.source.left
  have hRank : ∀ r, IsFiniteLocallyFreeOfRank (pullback.snd G.source.left (U r).ι) r :=
    fun r => rank_pullbackSnd_of_morphismRestrict G.source.left (U r) r (hRestrict r)
  have hzero : U 0 = ⊥ := source_rank_zero_open_eq_bot G (U 0) (hRank 0)
  have hInv : ∀ r, IsInvariantOpen G (U r) := by
    intro r z hz
    have hzCover : G.target.left z ∈ (⨆ d, U d) := hdec.iSup_eq_top ▸ trivial
    rw [Opens.mem_iSup] at hzCover
    obtain ⟨d, hd⟩ := hzCover
    exact rank_eq_of_arrow G U hRank z hz hd ▸ hd
  refine ⟨U, hzero, fun r => (hdec.isClopen r).1, fun i j hij => hdec.disjoint i j hij,
    hdec.iSup_eq_top, fun r => ⟨hInv r, ?_⟩⟩
  let g : Over.mk ((U r).ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk (U r).ι
  let H := GroupoidScheme.restrict G g
  let eA : H.groupoid.arrows.left ≅ (restrictionArrows G g).left :=
    (Over.forget S).mapIso (eqToIso H.arrows_eq)
  let eO : H.groupoid.objects.left ≅ (Over.mk ((U r).ι ≫ G.objects.hom)).left :=
    (Over.forget S).mapIso (eqToIso H.objects_eq)
  obtain ⟨e, he⟩ := restriction_arrows_iso_source_open G (U r) (hInv r) g rfl
  have hsourceIso : H.groupoid.source.left =
      eA.hom ≫ (restrictionSource G g).left ≫ eO.symm.hom := by
    simpa [eA, eO, Category.assoc] using congrArg Over.Hom.left H.source_eq
  let eR : H.groupoid.arrows.left ≅ pullback G.source.left (U r).ι := eA ≪≫ e
  have hSource : IsFiniteLocallyFreeOfRank H.groupoid.source.left r := by
    have : IsFiniteLocallyFreeOfRank (pullback.snd G.source.left (U r).ι) r := hRank r
    have heR : eR.hom ≫ pullback.snd G.source.left (U r).ι =
        H.groupoid.source.left ≫ eO.hom := by
      dsimp only [eR]
      rw [Iso.trans_hom, Category.assoc, he, hsourceIso]
      simp
    have h := rank_of_source_iso eR (pullback.snd G.source.left (U r).ι) r
    have h' : IsFiniteLocallyFreeOfRank
        ((eR.hom ≫ pullback.snd G.source.left (U r).ι) ≫ eO.symm.hom) r :=
      rank_post_iso (eR.hom ≫ pullback.snd G.source.left (U r).ι) eO.symm r
    rw [heR] at h'
    simpa [Category.assoc] using h'
  refine ⟨hSource, ?_⟩
  have : IsFiniteLocallyFreeOfRank H.groupoid.source.left r := hSource
  have : IsIso H.groupoid.inverse.left := groupoidInverse_left_isIso H.groupoid
  have h := rank_of_source_iso (asIso H.groupoid.inverse.left) H.groupoid.source.left r
  have heq : H.groupoid.inverse.left ≫ H.groupoid.source.left = H.groupoid.target.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left H.groupoid.source_inverse
  rwa [show (asIso H.groupoid.inverse.left).hom = H.groupoid.inverse.left from rfl, heq] at h

end AlgebraicGeometry.GroupoidScheme

end

end
