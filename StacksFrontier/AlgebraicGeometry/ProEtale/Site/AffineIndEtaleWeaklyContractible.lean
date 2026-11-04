module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.Permanence
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCoverCardinality
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenRefinement
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSiteCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough weakly contractible objects in the affine ind-étale pro-étale site

Let `S` be an affine object of a chosen big pro-étale site. Every object of the affine
ind-étale site `S_app` is covered by a single object which is quasi-compact and weakly
contractible, so that site has enough quasi-compact weakly contractible objects.

Both properties come from one construction. An object `U` of `S_app` is affine, and the ring
of global sections of an affine scheme has a faithfully flat ind-étale w-contractible
extension of bounded cardinality; the spectrum of that extension is again small enough for the
chosen big site and ind-étale over `S`, so it is an object of `S_app` covering `U`.
Quasi-compactness of every object of `S_app` is formal: its covering families are finite by
definition and satisfy the site axioms. Weak contractibility of the constructed object follows
from w-contractibility of its ring of global sections, which refines each of its covering
sieves by a finite disjoint clopen Zariski cover.

## Main results

* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isSite_isCovering`: the standard
  pro-étale covering families of the affine ind-étale site satisfy the site axioms.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isQuasiCompactObject`: every object of
  the affine ind-étale site is quasi-compact.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isWeaklyContractible_of_isWContractible`:
  an object whose ring of global sections is w-contractible is weakly contractible in the
  affine ind-étale site.
* `AlgebraicGeometry.ProEtale.exists_affine_indEtale_wContractible_cover`: an affine object of
  a chosen big pro-étale site is covered by a single affine ind-étale object with
  w-contractible global sections.
* `AlgebraicGeometry.ProEtale.affineIndEtaleProetale_hasEnough_quasiCompact_weaklyContractible`:
  the affine ind-étale site of an affine base has enough quasi-compact weakly contractible
  objects.

## Implementation notes

The index bound a chosen big site imposes on its covering families is not stable under
restricting a family to a subfamily of its index type, so a finite family is replaced by its
reindexing along the set of pairs (source, structure morphism) it realizes, which generates
the same presieve and is bounded because it injects into the index type of a chosen
representative.

## References

* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : B.Scheme)

namespace AffineIndEtaleProetale

/-- Precomposing the structure morphism of an object `U` of the affine ind-étale site with a
morphism which is ind-étale on global sections is ind-étale on global sections. -/
private theorem ind_etale_appTop_comp_hom (U : AffineIndEtaleProetale B S) {X : B.Scheme}
    {g : X ⟶ U.obj.obj.left} (hg : CommRingCat.etale.ind.{u} (B.inclusion.map g).appTop) :
    CommRingCat.etale.ind.{u} (B.inclusion.map (g ≫ U.obj.obj.hom)).appTop := by
  rw [B.inclusion.map_comp, Scheme.Hom.comp_appTop]
  exact CommRingCat.ind_etale_comp _ _
    ((MorphismProperty.ind_iff_ind_underMk _).mpr U.property.2) hg

/-- Precomposing the structure morphism of an object `U` of the affine ind-étale site with a
weakly étale morphism is weakly étale. -/
private theorem weaklyEtale_map_comp_hom (U : AffineIndEtaleProetale B S) {X : B.Scheme}
    {g : X ⟶ U.obj.obj.left} (hg : WeaklyEtale (B.inclusion.map g)) :
    WeaklyEtale (B.inclusion.map (g ≫ U.obj.obj.hom)) := by
  have : WeaklyEtale (B.inclusion.map U.obj.obj.hom) := U.obj.property
  rw [B.inclusion.map_comp]
  infer_instance

/-- **Stacks 098X.** The standard pro-étale covering families of the affine ind-étale site
satisfy the isomorphism, composition and base change axioms. -/
theorem isSite_isCovering : IsSite (IsCovering B S) := by
  let K := inclusion B S ⋙ SmallProetale.inclusion B S.obj S.property ⋙
    BigProetaleOver.forget B S.obj S.property
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    exact ⟨B.covering_isSite.1 (K.map f), inferInstance⟩
  · intro E hE F hF h
    have hcomp := B.covering_isSite.2.1
      ⟨K.obj E.1, E.2.map K⟩ hE.1
      (fun i ↦ ⟨K.obj (F i).1, (F i).2.map K⟩)
      (fun i ↦ (hF i).1) (fun i ↦ congrArg K.obj (h i))
    refine ⟨?_, ?_⟩
    · simpa [IsCovering, SmallProetale.IsCovering, BigProetaleOver.IsCovering, K,
        PreZeroHypercover.map, PreZeroHypercover.bind,
        PreZeroHypercover.pushforward] using hcomp
    · have hEfin : Finite E.2.I₀ := hE.2
      have hFfin : ∀ i, Finite (F i).2.I₀ := fun i ↦ (hF i).2
      show Finite (Σ i, (F i).2.I₀)
      infer_instance
  · intro E hE V g
    obtain ⟨P, a, b, hpb, hcov⟩ := B.covering_isSite.2.2
      ⟨K.obj E.1, E.2.map K⟩ hE.1
      (K.obj V) (K.map g)
    have hVaff : IsAffine (B.inclusion.obj (K.obj V)) := V.property.1
    have hEaff : IsAffine (B.inclusion.obj (K.obj E.1)) := E.1.property.1
    have hPaff (i : E.2.I₀) : IsAffine (B.inclusion.obj (P i)) := by
      have h₁ : IsAffine (B.inclusion.obj (K.obj (E.2.X i))) :=
        (E.2.X i).property.1
      have h₄ : IsAffine (B.inclusion.obj ((E.2.map K).X i)) :=
        (E.2.X i).property.1
      exact IsAffine.of_isPullback ((hpb i).map B.inclusion)
    have hind (i : E.2.I₀) : CommRingCat.etale.ind.{u}
        (B.inclusion.map (b i ≫ V.obj.obj.hom)).appTop := by
      have h₁ : IsAffine (B.inclusion.obj (K.obj (E.2.X i))) :=
        (E.2.X i).property.1
      have htri : (B.inclusion.map E.1.obj.obj.hom).appTop ≫
          (B.inclusion.map (K.map (E.2.f i))).appTop =
          (B.inclusion.map (E.2.X i).obj.obj.hom).appTop := by
        rw [← Scheme.Hom.comp_appTop, ← B.inclusion.map_comp]
        exact congrArg (fun f ↦ (B.inclusion.map f).appTop) (E.2.f i).hom.hom.w
      have ha : CommRingCat.etale.ind.{u}
          (B.inclusion.map (K.map (E.2.f i))).appTop := by
        rw [MorphismProperty.ind_iff_ind_underMk]
        refine CommRingCat.ind_etale_of_comp (B.inclusion.map E.1.obj.obj.hom).appTop _
          E.1.property.2 ?_
        rw [htri]; exact (E.2.X i).property.2
      have h₄ : IsAffine (B.inclusion.obj ((E.2.map K).X i)) :=
        (E.2.X i).property.1
      have hb : CommRingCat.etale.ind.{u} (B.inclusion.map (b i)).appTop :=
        MorphismProperty.IsStableUnderCobaseChange.of_isPushout
          (isPushout_appTop_of_isPullback ((hpb i).map B.inclusion)).flip ha
      exact ind_etale_appTop_comp_hom B S V hb
    have hweak (i : E.2.I₀) : WeaklyEtale (B.inclusion.map (b i ≫ V.obj.obj.hom)) := by
      have hEf : WeaklyEtale (B.inclusion.map (K.map (E.2.f i))) := by
        have hm := hE.1.1
        change ((E.2.map K).map B.inclusion).presieve₀ ∈
          Scheme.proetalePrecoverage _ at hm
        exact ((Scheme.presieve₀_mem_precoverage_iff _).mp hm.2).2 i
      have hbi : WeaklyEtale (B.inclusion.map (b i)) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback ((hpb i).map B.inclusion) hEf
      exact weaklyEtale_map_comp_hom B S V hbi
    let Q (i : E.2.I₀) : AffineIndEtaleProetale B S :=
      ⟨⟨Over.mk (b i ≫ V.obj.obj.hom), hweak i⟩,
        hPaff i, (MorphismProperty.ind_iff_ind_underMk _).mp (hind i)⟩
    let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
      ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk (a i) (by
        have hi := (hpb i).w
        change a i ≫ (E.2.f i).hom.hom.left = b i ≫ g.hom.hom.left at hi
        show a i ≫ (E.2.X i).obj.obj.hom = b i ≫ V.obj.obj.hom
        rw [← Over.w (E.2.f i).hom.hom, ← Over.w g.hom.hom]
        exact (reassoc_of% hi) _)))
    let q₂ (i : E.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk (b i) rfl))
    exact ⟨Q, q₁, q₂, fun i ↦ IsPullback.of_map_of_faithful K (hpb i), hcov, hE.2⟩

/-- **Stacks 090H** for the affine ind-étale site: every one of its objects is quasi-compact,
its covering families being finite by definition. -/
theorem isQuasiCompactObject (U : AffineIndEtaleProetale B S) :
    (topology B S).IsQuasiCompactObject U :=
  GrothendieckTopology.isQuasiCompactObject_of_isSite _ (isSite_isCovering B S)
    (fun _ h ↦ h.2) _ (fun _ _ ↦ Iff.rfl) U

end AffineIndEtaleProetale

/-- A finite covering family of a chosen big pro-étale site is reindexed by a type which
injects into the index type of a chosen combinatorial representative, so that the reindexed
family is itself a chosen covering family and generates the same presieve. -/
theorem BigProetaleSite.exists_finite_restrictIndex_covering {T : B.Scheme}
    (E : PreZeroHypercover.{u + 1} T) [Finite E.I₀] (hE : B.IsProetaleCovering ⟨T, E⟩) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (a : ι → E.I₀),
      B.covering ⟨T, E.restrictIndex a⟩ ∧
        (E.restrictIndex a).presieve₀ = E.presieve₀ := by
  classical
  let k : E.I₀ → (Σ X : B.Scheme, X ⟶ T) := fun i ↦ ⟨E.X i, E.f i⟩
  let ι := Set.range k
  choose a ha using fun p : ι ↦ p.property
  have hEq : (E.restrictIndex a).presieve₀ = E.presieve₀ := by
    refine le_antisymm (E.presieve₀_restrictIndex_le a) ?_
    rintro Y f ⟨i⟩
    have hp : (⟨E.X (a ⟨k i, ⟨i, rfl⟩⟩), E.f (a ⟨k i, ⟨i, rfl⟩⟩)⟩ : Σ X : B.Scheme, X ⟶ T) =
        ⟨E.X i, E.f i⟩ := ha ⟨k i, ⟨i, rfl⟩⟩
    exact (congrArg (fun p : Σ X : B.Scheme, X ⟶ T ↦ (E.restrictIndex a).presieve₀ p.2) hp) ▸
      (Presieve.ofArrows.mk _ : (E.restrictIndex a).presieve₀ (E.f (a ⟨k i, ⟨i, rfl⟩⟩)))
  obtain ⟨⟨T', G⟩, hG, heq, hcomb⟩ := B.covering_representatives ⟨T, E⟩ hE
  obtain rfl : T = T' := heq
  have hEG : E.presieve₀ = G.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb
  have hpair {Y : B.Scheme} {h : Y ⟶ T} (hh : G.presieve₀ h) :
      ∃ j, (⟨G.X j, G.f j⟩ : Σ X : B.Scheme, X ⟶ T) = ⟨Y, h⟩ := by
    cases hh with | mk j => exact ⟨j, rfl⟩
  have hex (p : ι) : ∃ j, (⟨G.X j, G.f j⟩ : Σ X : B.Scheme, X ⟶ T) = p.val := by
    have hm : G.presieve₀ (E.f (a p)) := by rw [← hEG]; exact Presieve.ofArrows.mk (a p)
    obtain ⟨j, hj⟩ := hpair hm
    exact ⟨j, hj.trans (ha p)⟩
  choose b hb using hex
  have hinj : Function.Injective b := fun i j hij ↦
    Subtype.ext <| by rw [← hb i, ← hb j, hij]
  refine ⟨ι, inferInstance, a, ⟨?_, ?_⟩, hEq⟩
  · show ((E.restrictIndex a).map B.inclusion).presieve₀ ∈ _
    rw [PreZeroHypercover.presieve₀_map, hEq, ← PreZeroHypercover.presieve₀_map]
    exact hE
  · exact (Cardinal.mk_le_of_injective hinj).trans hG.2

/-- An object of the affine ind-étale site whose ring of global sections is w-contractible is a
weakly contractible object of that site. -/
theorem AffineIndEtaleProetale.isWeaklyContractible_of_isWContractible
    (U : AffineIndEtaleProetale B S)
    (hW : IsWContractible.{u, u} Γ(U.obj.obj.left.obj, ⊤)) :
    (AffineIndEtaleProetale.topology B S).IsWeaklyContractible U := by
  classical
  let I := AffineIndEtaleProetale.inclusion B S ⋙ SmallProetale.inclusion B S.obj S.property
  let q := BigProetaleOver.forget B S.obj S.property
  let Q := I ⋙ q
  let J := AffineIndEtaleProetale.topology B S
  have hUaff : IsAffine U.obj.obj.left.obj := U.property.1
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  apply GrothendieckTopology.isWeaklyContractible_of_clopenRefinements J (Q ⋙ B.inclusion) U
  · intro Z hZ
    let E : PreZeroHypercover.{u + 1} Z :=
      ⟨ULift.{u + 1} Empty, fun i ↦ i.down.elim, fun i ↦ i.down.elim⟩
    have hE : AffineIndEtaleProetale.IsCovering B S ⟨Z, E⟩ := by
      refine ⟨⟨?_, ?_⟩, inferInstance⟩
      · show ((E.map Q).map B.inclusion).presieve₀ ∈ _
        apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
        rw [Scheme.zariskiPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ (hZ.false x).elim, fun i ↦ i.down.elim⟩
      · simp only [E, PreZeroHypercover.map_I₀, Cardinal.mk_eq_zero, zero_le]
    have heq : E.sieve₀ = ⊥ := by
      ext X f
      refine ⟨fun hf ↦ ?_, False.elim⟩
      obtain ⟨i, -, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
      exact i.down.elim
    rw [← heq]
    exact Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  · intro X Y f hf
    exact I.mono_of_mono_map (q.mono_of_mono_map (B.inclusion.mono_of_mono_map hf))
  · intro T hT
    obtain ⟨E, hE, hET⟩ := exists_covering_le_of_isSite (AffineIndEtaleProetale.IsCovering B S)
      (AffineIndEtaleProetale.isSite_isCovering B S) (AffineIndEtaleProetale.precoverage B S)
      (fun _ _ ↦ Iff.rfl) T hT
    have hT' : T.functorPushforward Q ∈ B.topology (Q.obj U) := by
      refine B.topology.superset_covering (Sieve.functorPushforward_monotone Q U
        ((Sieve.generate_le_iff _ _).mpr hET)) ?_
      rw [← PreZeroHypercover.sieve₀_map]
      exact Precoverage.generate_mem_toGrothendieck ⟨E.map Q, rfl, hE.1⟩
    obtain ⟨n, V, g, hdec, href⟩ :=
      exists_clopenRefinement_of_isWContractible B U.obj.obj.left hW _ hT'
    have hVaffine (i : Fin n) : IsAffine (V i).obj := by
      have h₁ : IsAffine (B.inclusion.obj U.obj.obj.left) := U.property.1
      have h₂ : IsOpenImmersion (B.inclusion.map (g i)) := hdec.openImmersion i
      have h₃ : IsClosedImmersion (B.inclusion.map (g i)) :=
        IsClosedImmersion.of_isPreimmersion _ (hdec.clopen i).isClosed
      exact (IsClosedImmersion.isAffine_surjective_of_isAffine (B.inclusion.map (g i))).1
    have hwind (i : Fin n) : IsAffineIndEtale B S
        ⟨Over.mk (g i ≫ U.obj.obj.hom), by
          have h₁ : IsOpenImmersion (B.inclusion.map (g i)) := hdec.openImmersion i
          exact weaklyEtale_map_comp_hom B S U inferInstance⟩ := by
      refine ⟨hVaffine i, ?_⟩
      refine (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale)
        (B.inclusion.map (g i ≫ U.obj.obj.hom)).appTop).mp
        (ind_etale_appTop_comp_hom B S U ?_)
      have h₁ : IsAffine (B.inclusion.obj (V i)) := hVaffine i
      have h₂ : IsAffine (B.inclusion.obj U.obj.obj.left) := U.property.1
      have h₃ : IsOpenImmersion (B.inclusion.map (g i)) := hdec.openImmersion i
      exact MorphismProperty.le_ind _ _
        (HasRingHomProperty.appTop (P := @Etale) _ inferInstance)
    let X (i : Fin n) : AffineIndEtaleProetale B S := ⟨_, hwind i⟩
    let f (i : Fin n) : X i ⟶ U := I.preimage (Over.homMk (g i))
    have hQf (i : Fin n) : Q.map (f i) = g i := by
      dsimp only [Q, f, Functor.comp_map]; rw [Functor.map_preimage]; rfl
    let F : PreZeroHypercover.{u + 1} U :=
      ⟨ULift.{u + 1} (Fin n), fun i ↦ X i.down, fun i ↦ f i.down⟩
    have hF : B.IsProetaleCovering ⟨Q.obj U, F.map Q⟩ := by
      show ((F.map Q).map B.inclusion).presieve₀ ∈ _
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.zariskiPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
      · have hx : x ∈ ⋃ i, Set.range (B.inclusion.map (g i)).base :=
          (Set.ext_iff.mp hdec.cover x).mpr (Set.mem_univ x)
        obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
        refine ⟨ULift.up i, y, ?_⟩
        show (B.inclusion.map (Q.map (f i))).base y = x
        rwa [hQf]
      · show IsOpenImmersion (B.inclusion.map (Q.map (f i.down)))
        rw [hQf]; exact hdec.openImmersion i.down
    have hFQfin : Finite (F.map Q).I₀ := inferInstanceAs (Finite (ULift.{u + 1} (Fin n)))
    obtain ⟨ι, hfin, a, ha, -⟩ := B.exists_finite_restrictIndex_covering (F.map Q) hF
    have hFa : (F.restrictIndex a).sieve₀ ∈ J U :=
      Precoverage.generate_mem_toGrothendieck ⟨F.restrictIndex a, rfl, ha, hfin⟩
    have hFtop : F.sieve₀ ∈ J U :=
      J.superset_covering (Sieve.generate_mono (F.presieve₀_restrictIndex_le a)) hFa
    have hcover : Sieve.ofArrows X f ∈ J U := by
      refine J.superset_covering (fun Y b hb ↦ ?_) hFtop
      obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hb
      exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i.down, c, hc⟩
    refine ⟨n, X, f, ?_, hcover, fun i ↦ ?_⟩
    · show IsClopenDecompositionCover (fun i ↦ (V i).obj)
        (fun i ↦ B.inclusion.map (Q.map (f i)))
      simpa only [hQf] using hdec
    · obtain ⟨Z, c₁, c₂, hc₁, hc₂⟩ := href i
      let c : X i ⟶ Z := I.preimage (Over.homMk c₂ (by
        have hw : Q.map c₁ ≫ U.obj.obj.hom = Z.obj.obj.hom := c₁.hom.hom.w
        show c₂ ≫ Z.obj.obj.hom = g i ≫ U.obj.obj.hom
        rw [← hw, ← Category.assoc, ← hc₂]))
      have hc : c ≫ c₁ = f i := by
        refine I.map_injective (q.map_injective ?_)
        show Q.map c ≫ Q.map c₁ = Q.map (f i)
        rw [hQf, show Q.map c = c₂ by
          dsimp only [Q, c, Functor.comp_map]; rw [Functor.map_preimage]; rfl]
        exact hc₂.symm
      rw [← hc]
      exact T.downward_closed hc₁ c

/-- **Stacks 0983** in the chosen big site, with everything the construction yields: an affine
object `T` is covered by a single affine object which is weakly étale, ind-étale and surjective
over `T`, has w-contractible ring of global sections, and has size at most
`Cardinal.proetaleBound` of the size of `T`. -/
theorem exists_affine_indEtale_wContractible_cover_surjective_size_le
    (T : B.Scheme) [IsAffine T.obj] :
    ∃ (V : B.Scheme) (g : V ⟶ T),
      B.covering ⟨T, PreZeroHypercover.singleton g⟩ ∧ IsAffine V.obj ∧
        IsWContractible.{u, u} Γ(V.obj, ⊤) ∧
        CommRingCat.etale.ind.{u} (B.inclusion.map g).appTop ∧
        WeaklyEtale (B.inclusion.map g) ∧
        Surjective (B.inclusion.map g) ∧
        V.obj.size ≤ Cardinal.proetaleBound T.obj.size := by
  classical
  let A := Γ(T.obj, ⊤)
  let κ := T.obj.size
  have hκ : Cardinal.aleph0 ≤ κ := by
    show Cardinal.aleph0 ≤ T.obj.size
    rw [Scheme.size_of_isAffine T.obj]; exact le_max_left _ _
  have hA : Cardinal.mk A ≤ κ := by
    show Cardinal.mk Γ(T.obj, ⊤) ≤ T.obj.size
    rw [Scheme.size_of_isAffine T.obj]; exact le_max_right _ _
  obtain ⟨D, hD, f, hff, hind, hwd, hDmk⟩ :=
    exists_small_faithfullyFlat_ind_etale_wContractible A κ hκ hA
  let _ : CommRing D := hD
  let _ : Algebra A D := f.toAlgebra
  let r : A ⟶ CommRingCat.of D := CommRingCat.ofHom f
  have hri : CommRingCat.etale.ind.{u} r :=
    (MorphismProperty.ind_iff_ind_underMk _).mpr hind
  have hweak : Algebra.WeaklyEtale A D := Algebra.weaklyEtale_of_ind_etale
    (StacksDraft.indEtale_iff.mpr (CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hri))
  have hwe := (Algebra.weaklyEtale_iff A D).mp hweak
  have hDsize : (Spec (CommRingCat.of D)).size ≤ Cardinal.proetaleBound κ := by
    rw [Scheme.size_Spec]
    refine max_le ?_ (hDmk.trans (le_max_left _ _))
    exact hκ.trans ((Cardinal.self_le_power κ Cardinal.one_le_aleph0).trans
      ((le_max_left _ _).trans (le_max_right _ _)))
  let V : B.Scheme := ⟨Spec (CommRingCat.of D), B.closed_under_proetaleBound T.property hDsize⟩
  let e := T.obj.isoSpec
  let g₀ : V.obj ⟶ T.obj := Spec.map r ≫ e.inv
  let g : V ⟶ T := B.inclusion.preimage g₀
  have hg : B.inclusion.map g = g₀ := B.inclusion.map_preimage _
  have hflat : Flat (Spec.map r) := ((flat_and_surjective_SpecMap_iff r).mpr hff).1
  have hsurj : Surjective (Spec.map r) := ((flat_and_surjective_SpecMap_iff r).mpr hff).2
  have hdiag : Flat (pullback.diagonal (Spec.map r)) := by
    show Flat (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A D))))
    rw [diagonal_SpecMap A D]
    have hm : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' A (S := D)).toRingHom)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact hwe.2
    exact MorphismProperty.comp_mem _ _ _ hm inferInstance
  have hwer : WeaklyEtale (Spec.map r) := ⟨hflat, hdiag⟩
  have hweg : WeaklyEtale g₀ := inferInstance
  have hsurjg : Surjective g₀ := inferInstance
  have hqcg : QuasiCompact g₀ := quasiCompact_of_compactSpace _
  have hcov : B.covering ⟨T, PreZeroHypercover.singleton g⟩ := by
    refine ⟨?_, (B.covering_isSite.1 (𝟙 T)).2⟩
    show ((PreZeroHypercover.singleton g).map B.inclusion).presieve₀ ∈ _
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_singleton,
      Presieve.map_singleton, hg]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (inferInstance : WeaklyEtale g₀)
  have hglobal : Scheme.proetaleTopology.IsWeaklyContractible V.obj :=
    ((main_theorem D).out 1 2).mp hwd
  refine ⟨V, g, hcov, inferInstance,
    isWContractible_of_isWeaklyContractible V.obj hglobal, ?_, by rw [hg]; infer_instance,
    by rw [hg]; infer_instance, hDsize⟩
  rw [hg]
  show CommRingCat.etale.ind.{u} (Spec.map r ≫ e.inv).appTop
  rw [Scheme.Hom.comp_appTop]
  have hiso : IsIso e.inv.appTop := Functor.map_isIso Scheme.Γ e.inv.op
  exact MorphismProperty.RespectsIso.precomp _ _ _
    ((MorphismProperty.arrow_mk_iso_iff CommRingCat.etale.ind (arrowIsoΓSpecOfIsAffine r)).mp hri)

/-- **Stacks 0983** in the chosen big site: an affine object `T` is covered by a single affine
object which is weakly étale and ind-étale over `T` and whose ring of global sections is
w-contractible. -/
theorem exists_affine_indEtale_wContractible_cover (T : B.Scheme) [IsAffine T.obj] :
    ∃ (V : B.Scheme) (g : V ⟶ T),
      B.covering ⟨T, PreZeroHypercover.singleton g⟩ ∧ IsAffine V.obj ∧
        IsWContractible.{u, u} Γ(V.obj, ⊤) ∧
        CommRingCat.etale.ind.{u} (B.inclusion.map g).appTop ∧
        WeaklyEtale (B.inclusion.map g) := by
  obtain ⟨V, g, hcov, haff, hwc, hind, hwe, -, -⟩ :=
    exists_affine_indEtale_wContractible_cover_surjective_size_le B T
  exact ⟨V, g, hcov, haff, hwc, hind, hwe⟩

/-- **Stacks 0990, the affine ind-étale pro-étale site.** For an affine base, the affine
ind-étale pro-étale site has enough quasi-compact weakly contractible objects: every object is
covered by a single object which is quasi-compact and weakly contractible. -/
@[stacks 0990 "affine ind-étale pro-étale site"]
theorem affineIndEtaleProetale_hasEnough_quasiCompact_weaklyContractible [IsAffine S.obj] :
    (AffineIndEtaleProetale.topology B S).HasEnoughObjects
      (fun U : AffineIndEtaleProetale B S ↦
        (AffineIndEtaleProetale.topology B S).IsQuasiCompactObject U ∧
        (AffineIndEtaleProetale.topology B S).IsWeaklyContractible U) := by
  classical
  intro U
  have hUaff : IsAffine U.obj.obj.left.obj := U.property.1
  obtain ⟨V, g, hcov, haff, hw, hi, hwe⟩ :=
    exists_affine_indEtale_wContractible_cover B U.obj.obj.left
  have hweg : WeaklyEtale (B.inclusion.map g) := hwe
  let W : AffineIndEtaleProetale B S :=
    ⟨⟨Over.mk (g ≫ U.obj.obj.hom), AffineIndEtaleProetale.weaklyEtale_map_comp_hom B S U hwe⟩,
      haff, (MorphismProperty.ind_iff_ind_underMk _).mp
        (AffineIndEtaleProetale.ind_etale_appTop_comp_hom B S U hi)⟩
  let f : W ⟶ U := ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk g))
  let E : PreZeroHypercover.{u + 1} U := PreZeroHypercover.singleton f
  have hE : AffineIndEtaleProetale.IsCovering B S ⟨U, E⟩ := ⟨hcov, inferInstance⟩
  have htop : E.sieve₀ ∈ AffineIndEtaleProetale.topology B S U :=
    Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  refine ⟨PUnit.{u + 1}, (fun _ ↦ W), (fun _ ↦ f), ?_, fun _ ↦ ?_⟩
  · simpa [E, PreZeroHypercover.sieve₀, Sieve.ofArrows, Presieve.ofArrows_pUnit] using htop
  · exact ⟨AffineIndEtaleProetale.isQuasiCompactObject B S W,
      AffineIndEtaleProetale.isWeaklyContractible_of_isWContractible B S W hw⟩

end AlgebraicGeometry.ProEtale

end
