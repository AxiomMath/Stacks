module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocallyClosedStratum
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsEveryRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Locally Noetherian decent algebraic spaces are quasi-separated

Let `X` be an algebraic space over a scheme `S`. If `X` is locally Noetherian and decent, then
`X` is quasi-separated, in the absolute sense, over the terminal scheme.

## Main results

* `AlgebraicGeometry.Space.presheafQuasiCompact_of_affine_etale_chart`: an affine étale chart of
  a locally Noetherian decent algebraic space is quasi-compact.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isLocallyNoetherian_of_isDecentSpace`:
  a locally Noetherian decent algebraic space is quasi-separated.

## References

* [Stacks Project, Tag 0BB6](https://stacks.math.columbia.edu/tag/0BB6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- In a family `Z 0 = ∅, …, Z (n+1) = univ` of sets every point lies in some difference
`Z k.succ \ Z k.castSucc`. -/
private lemma exists_mem_filtration_stratum {α : Type*} (n : ℕ)
    (Z : Fin (n + 2) → Set α) (hzero : Z 0 = ∅)
    (hlast : Z (Fin.last (n + 1)) = Set.univ) (x : α) :
    ∃ k : Fin (n + 1), x ∈ Z k.succ \ Z k.castSucc := by
  classical
  let Q (j : ℕ) : Prop := ∃ hj : j ≤ n + 1, x ∈ Z ⟨j, by omega⟩
  have hex : ∃ j, Q j := ⟨n + 1, le_rfl, (congrArg (x ∈ ·) hlast).mpr trivial⟩
  let m := Nat.find hex
  obtain ⟨hmbound, hmrange⟩ := Nat.find_spec hex
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun hm => by
    rw [show (⟨m, by omega⟩ : Fin (n + 2)) = 0 from Fin.ext hm, hzero] at hmrange
    exact hmrange
  have hprev : x ∉ Z ⟨m - 1, by omega⟩ := fun hx =>
    Nat.find_min hex (show m - 1 < m by omega) ⟨by omega, hx⟩
  refine ⟨⟨m - 1, by omega⟩, ?_, hprev⟩
  convert hmrange using 2
  exact Fin.ext (by dsimp; omega)

/-- A flat, locally finitely presented, separated and locally quasi-finite morphism with
universally bounded fibres over a Noetherian base has quasi-compact source. -/
private theorem compactSpace_of_hasUniversallyBoundedFibers
    {W D : Scheme.{u}} (g : W ⟶ D) [Flat g] [LocallyOfFinitePresentation g]
    [_root_.AlgebraicGeometry.IsSeparated g] [LocallyQuasiFinite g]
    (hbounded : _root_.AlgebraicGeometry.HasUniversallyBoundedFibers g)
    [CompactSpace D] [IsLocallyNoetherian D] : CompactSpace W := by
  have _ : IsNoetherian D := ⟨⟩
  obtain ⟨n, Z, hclosed, hzero, hlast, -, hchar⟩ :=
    exists_closed_filtration_characterizing_finiteLocallyFree_rank g hbounded
  have hLC (r : Fin (n + 1)) : IsLocallyClosed (Z r.succ ∩ (Z r.castSucc)ᶜ) :=
    (hclosed _).isLocallyClosed.inter (isOpen_compl_iff.mpr (hclosed _)).isLocallyClosed
  set T : Fin (n + 1) → Scheme.{u} := fun r => Scheme.locallyClosedSubscheme (hLC r) with hT
  set i : ∀ r, T r ⟶ D := fun r => Scheme.locallyClosedSubschemeι (hLC r) with hi
  have hrange (r : Fin (n + 1)) :
      Set.range (i r).base = Z r.succ \ Z r.castSucc := by
    rw [hi, Scheme.range_locallyClosedSubschemeι, Set.sdiff_eq]
  have hcompactT (r : Fin (n + 1)) : CompactSpace (T r) := by
    have _ : _root_.AlgebraicGeometry.IsImmersion (i r) :=
      inferInstanceAs
        (_root_.AlgebraicGeometry.IsImmersion (Scheme.locallyClosedSubschemeι (hLC r)))
    have hcompactRange : IsCompact (Set.range (i r).base) := by
      rw [hrange]
      exact TopologicalSpace.NoetherianSpace.isCompact _
    have himage : IsCompact ((i r).base '' (Set.univ : Set (T r))) := by
      simpa only [Set.image_univ, Set.range] using hcompactRange
    exact isCompact_univ_iff.mp ((i r).isEmbedding.isCompact_iff.mpr himage)
  have hcompactPiece (r : Fin (n + 1)) :
      IsCompact (Set.range (pullback.fst g (i r)).base) := by
    have _ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (pullback.snd g (i r)) r.val := (hchar r (T r) (i r)).2 (by rw [hrange])
    have _ : CompactSpace (T r) := hcompactT r
    have _ : QuasiCompact (pullback.snd g (i r)) := inferInstance
    have _ : CompactSpace (Limits.pullback g (i r) : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd g (i r))
    simpa only [Set.image_univ, Set.range] using
      (isCompact_univ : IsCompact (Set.univ : Set (Limits.pullback g (i r) : Scheme.{u}))).image
        (Limits.pullback.fst g (i r)).continuous
  have hcover : (Set.univ : Set W) = ⋃ r : Fin (n + 1), Set.range (pullback.fst g (i r)).base := by
    ext x
    refine ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩
    obtain ⟨r, hx⟩ := exists_mem_filtration_stratum n Z hzero hlast (g.base x)
    rw [Set.mem_iUnion]
    refine ⟨r, ?_⟩
    rw [Scheme.Pullback.range_fst]
    show g.base x ∈ Set.range (i r).base
    rwa [hrange]
  have hcompactUnion : IsCompact
      (⋃ r : Fin (n + 1), Set.range (pullback.fst g (i r)).base) := by
    simpa using Set.Finite.isCompact_biUnion
      (Set.toFinite (Set.univ : Set (Fin (n + 1)))) (fun r _ => hcompactPiece r)
  exact isCompact_univ_iff.mp (hcover ▸ hcompactUnion)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The projection of a fibre product onto one factor is separated as soon as the *other*
factor has separated underlying scheme. -/
private lemma isSeparated_map_of_isPullback
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {C D W : BigFppfOver B S hS}
    (p : W ⟶ D) (q : W ⟶ C) (d : yoneda.obj D ⟶ X) (c : yoneda.obj C ⟶ X)
    (hpb : IsPullback (yoneda.map p) (yoneda.map q) d c)
    (hC : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj C)) :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  set F := BigFppfOver.toScheme B S hS with hF
  have hCsep : _root_.AlgebraicGeometry.IsSeparated (F.map (terminal.from C)) := inferInstance
  set a := terminal.from D with ha
  set b := terminal.from C with hb
  set j : W ⟶ Limits.pullback a b := Limits.pullback.lift p q (Subsingleton.elim _ _) with hj
  have hjmono : Mono j := by
    refine ⟨fun i k hik => yoneda.map_injective (hpb.hom_ext ?_ ?_)⟩
    · simpa only [← Functor.map_comp, hj, Category.assoc, Limits.pullback.lift_fst] using
        congrArg (fun z => yoneda.map (z ≫ Limits.pullback.fst a b)) hik
    · simpa only [← Functor.map_comp, hj, Category.assoc, Limits.pullback.lift_snd] using
        congrArg (fun z => yoneda.map (z ≫ Limits.pullback.snd a b)) hik
  have hfst : _root_.AlgebraicGeometry.IsSeparated (F.map (Limits.pullback.fst a b)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsSeparated)
      ((IsPullback.of_hasPullback a b).map F).flip hCsep
  have _ : Mono (F.map j) := inferInstance
  have hcomp : _root_.AlgebraicGeometry.IsSeparated
      (F.map j ≫ F.map (Limits.pullback.fst a b)) := inferInstance
  simpa only [← Functor.map_comp, hj, Limits.pullback.lift_fst] using hcomp

/-- The base change of a chart along a composite `h_E ⟶ h_D ⟶ X` is represented by the fibre
product, formed in the site, of the base change along `h_D ⟶ X` with `E ⟶ D`. -/
private lemma exists_iso_pullback_comp
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {C D E : BigFppfOver B S hS}
    {c : yoneda.obj C ⟶ X} (hrep : yoneda.relativelyRepresentable c)
    (d : yoneda.obj D ⟶ X) (j : E ⟶ D) :
    ∃ e : Limits.pullback (hrep.snd d) j ≅ hrep.pullback (yoneda.map j ≫ d),
      e.hom ≫ hrep.snd (yoneda.map j ≫ d) = Limits.pullback.snd (hrep.snd d) j := by
  have hsq1 : IsPullback (yoneda.map (Limits.pullback.snd (hrep.snd d) j))
      (yoneda.map (Limits.pullback.fst (hrep.snd d) j)) (yoneda.map j)
      (yoneda.map (hrep.snd d)) :=
    ((IsPullback.of_hasPullback (hrep.snd d) j).flip).map yoneda
  have hA := (hsq1.paste_vert (hrep.isPullback' d).flip).flip
  have hB := hrep.isPullback' (yoneda.map j ≫ d)
  refine ⟨yoneda.preimageIso (hA.isoIsPullback _ _ hB), yoneda.map_injective ?_⟩
  rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
  exact hA.isoIsPullback_hom_snd _ _ hB

/-- The fibre of an étale chart with affine source, over the canonical residue-field point of
a point of another chart, is finite locally free of some degree on a decent algebraic space. -/
private lemma exists_isFiniteLocallyFreeOfRank_pullback_fst_schemePoint
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {C D : BigFppfOver B S hS}
    (hC : CompactSpace ((BigFppfOver.toScheme B S hS).obj C))
    {c : yoneda.obj C ⟶ X}
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (d : yoneda.obj D ⟶ X) (y : (BigFppfOver.toScheme B S hS).obj D) :
    ∃ (k : Type u) (_ : Field k) (κ : Spec (CommRingCat.of k) ⟶
        (BigFppfOver.toScheme B S hS).obj D) (r : ℕ),
      κ.base (default : Spec (CommRingCat.of k)) = y ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (Limits.pullback.fst κ
          ((BigFppfOver.toScheme B S hS).map (hc.rep.snd d))) r := by
  let F := BigFppfOver.toScheme B S hS
  have _ : PreservesLimitsOfShape WalkingCospan F := by apply comp_preservesLimitsOfShape
  set w := hc.rep.snd d with hw
  set pD := schemePointRepresentative B S hS D y
  set κ₀ : FieldValuedPoint.siteObject B S hS (yoneda.obj D) pD ⟶ D := pD.value with hκ₀
  set p : FieldValuedPoint B S hS X :=
    { carrier := pD.carrier, contained := pD.contained, toBase := pD.toBase,
      value := yonedaEquiv (yoneda.map κ₀ ≫ d) } with hp
  have hξ : fieldMorphism B S hS X p = yoneda.map κ₀ ≫ d := Equiv.symm_apply_apply _ _
  have hqc : IsQuasiCompact B S hS (fieldMorphism B S hS X p) :=
    (hdec (p.class B S hS X)).everyFieldRepresentativeIsQuasiCompact B S hS X hX p rfl
  obtain ⟨r, hr⟩ :=
    exists_isFiniteLocallyFreeOfRank_snd_fieldMorphism B S hS p hqc hC c hc
  refine ⟨pD.carrier, pD.field, F.map κ₀, r, ?_, ?_⟩
  · have hpt : schemePoint B S hS D pD = y := schemePointRepresentative_point B S hS D y
    rw [Subsingleton.elim (default : Spec (CommRingCat.of pD.carrier))
      (IsLocalRing.closedPoint pD.carrier)]
    exact hpt
  · obtain ⟨e', he'hom⟩ := exists_iso_pullback_comp B S hS hc.rep d κ₀
    have hsq2 : IsPullback (F.map (Limits.pullback.snd w κ₀))
        (F.map (Limits.pullback.fst w κ₀)) (F.map κ₀) (F.map w) :=
      ((IsPullback.of_hasPullback w κ₀).flip).map F
    set e₂ := hsq2.isoIsPullback _ _ (IsPullback.of_hasPullback (F.map κ₀) (F.map w)) with he₂
    have he₂hom : e₂.hom ≫ Limits.pullback.fst (F.map κ₀) (F.map w) =
        F.map (Limits.pullback.snd w κ₀) :=
      hsq2.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback (F.map κ₀) (F.map w))
    have hkey : e₂.hom ≫ Limits.pullback.fst (F.map κ₀) (F.map w) =
        F.map e'.hom ≫ F.map (hc.rep.snd (yoneda.map κ₀ ≫ d)) := by
      rw [he₂hom, ← Functor.map_comp, he'hom]
    have hr' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (F.map e'.hom ≫ F.map (hc.rep.snd (yoneda.map κ₀ ≫ d))) r := by
      refine ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r).cancel_left_of_respectsIso
        (F.map e'.hom) _).2 ?_
      rwa [hξ] at hr
    rw [← hkey] at hr'
    exact ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r).cancel_left_of_respectsIso
      e₂.hom _).1 hr'

/-- The fibre product of an affine étale chart `C ⟶ X` of a decent algebraic space with a
morphism `D ⟶ X` from an affine, locally Noetherian object is quasi-compact. -/
private theorem compactSpace_pullback_of_affine_etale_charts
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {C D : BigFppfOver B S hS}
    (hC : IsAffine ((BigFppfOver.toScheme B S hS).obj C))
    (hD : IsAffine ((BigFppfOver.toScheme B S hS).obj D))
    (hDN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj D))
    {c : yoneda.obj C ⟶ X} (d : yoneda.obj D ⟶ X)
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (hc.rep.pullback d)) := by
  classical
  let F := BigFppfOver.toScheme B S hS
  have _ : CompactSpace (F.obj C) := inferInstance
  have _ : Etale (F.map (hc.rep.snd d)) := hc.property_snd d
  obtain ⟨_, _⟩ := locallyQuasiFinite_of_etale (F.map (hc.rep.snd d))
  have _ : _root_.AlgebraicGeometry.IsSeparated (F.map (hc.rep.snd d)) :=
    isSeparated_map_of_isPullback B S hS (hc.rep.snd d) (hc.rep.fst' d) d c
      (hc.rep.isPullback' d).flip inferInstance
  obtain ⟨Z, -, hZanti, hZiff⟩ :=
    exists_antitone_opens_iff_fiber_degree_ge (F.map (hc.rep.snd d))
  have hnot : ∀ y : F.obj D, ∃ m : ℕ, y ∉ Z m := by
    intro y
    obtain ⟨k, hk, κ, r, hκy, hr⟩ :=
      exists_isFiniteLocallyFreeOfRank_pullback_fst_schemePoint B S hS hX hdec
        inferInstance hc d y
    refine ⟨r + 1, fun hy => ?_⟩
    have hfac : ∃ h : Spec (CommRingCat.of k) ⟶ (Z (r + 1)).toScheme,
        h ≫ (Z (r + 1)).ι = κ := by
      rw [factors_through_open_iff_mem]
      exact hκy ▸ hy
    rcases (hZiff (r + 1) k κ).1 hfac with hnf | ⟨r', hr', hrank'⟩
    · refine hnf ?_
      have hflf := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
        (Limits.pullback.fst κ (F.map (hc.rep.snd d))) r (h := hr)
      exact ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        _).1 hflf).1
    · exact not_isFiniteLocallyFreeOfRank_of_rank_le _ hr le_rfl r' hr' hrank'
  have _ : IsNoetherian (F.obj D) := ⟨⟩
  have hfin : (genericPoints (F.obj D)).Finite :=
    genericPoints.finite finite_irreducibleComponents_of_isNoetherian
  choose m hm using hnot
  set N := hfin.toFinset.sup m with hN
  have hempty : ∀ y : F.obj D, y ∉ Z N := by
    intro y hy
    set Zc : irreducibleComponents (F.obj D) :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩ with hZc
    set η : genericPoints (F.obj D) := genericPoints.ofComponent Zc with hη
    have hηy : η.1 ⤳ y :=
      (genericPoints.isGenericPoint_ofComponent Zc).specializes
        (mem_irreducibleComponent (x := y))
    have hmem : η.1 ∈ Z N := hηy.mem_open (Z N).isOpen hy
    exact hm η.1 (hZanti (Finset.le_sup (hfin.mem_toFinset.mpr η.2)) hmem)
  refine compactSpace_of_hasUniversallyBoundedFibers (F.map (hc.rep.snd d)) ⟨(N : ℤ), ?_⟩
  rw [boundsFiberDegrees_iff_field_baseChange]
  intro k _ gk
  have hnotfac : ¬ ∃ h : Spec (CommRingCat.of k) ⟶ (Z N).toScheme, h ≫ (Z N).ι = gk := by
    rw [factors_through_open_iff_mem]
    exact hempty _
  have hdegree := (not_congr (hZiff N k gk)).1 hnotfac
  rw [not_or, not_not] at hdegree
  have _ := hdegree.1
  obtain ⟨r, hrN, hrank⟩ :=
    exists_isFiniteLocallyFreeOfRank_le_of_isFinite
      (Limits.pullback.fst gk (F.map (hc.rep.snd d))) (N - 1)
      (fun r hr hcon => hdegree.2 ⟨r, by omega, hcon⟩)
  exact ⟨r, by exact_mod_cast Nat.le_of_lt_succ (by omega), hrank⟩

/-- An affine étale chart of an algebraic space which is decent and has a surjective étale atlas
with locally Noetherian source is quasi-compact after every represented base change. -/
theorem presheafQuasiCompact_of_affine_etale_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ X}
    (hasurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hAN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj A))
    {C : BigFppfOver B S hS} (hC : IsAffine ((BigFppfOver.toScheme B S hS).obj C))
    {c : yoneda.obj C ⟶ X}
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c := by
  let F := BigFppfOver.toScheme B S hS
  have _ : PreservesLimitsOfShape WalkingCospan F := by apply comp_preservesLimitsOfShape
  have _ : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      F).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  refine (presheaf_inverseImage_iff_atlas_snd B S hS
    (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) c hc.rep A a hasurj haetale).2 ?_
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro O hO
  set j := opensObjectι B S hS A O with hj
  set aO := yoneda.map j ≫ a with haO
  have hOaff : IsAffine (F.obj (opensObject B S hS A O)) := hO
  have hONoeth : IsLocallyNoetherian (F.obj (opensObject B S hS A O)) := by
    show IsLocallyNoetherian O.toScheme
    infer_instance
  have hjetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      F).presheaf (yoneda.map j) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) j).2 (by
        show Etale O.ι
        infer_instance)
  have hOetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      F).presheaf aO :=
    MorphismProperty.comp_mem _ _ _ hjetale haetale
  have hcpt : CompactSpace (F.obj (hc.rep.pullback aO)) :=
    compactSpace_pullback_of_affine_etale_charts B S hS hX hdec hC hOaff hONoeth aO hc
  obtain ⟨e, -⟩ := exists_iso_pullback_comp B S hS hc.rep a j
  have hcpt' : CompactSpace (F.obj (Limits.pullback (hc.rep.snd a) j)) :=
    QuasiCompact.compactSpace_of_compactSpace (F.map e.hom)
  set e₂ := ((IsPullback.of_hasPullback (hc.rep.snd a) j).map F).isoIsPullback _ _
    (IsPullback.of_hasPullback (F.map (hc.rep.snd a)) (F.map j)) with he₂
  have hcpt'' : CompactSpace
      (Limits.pullback (F.map (hc.rep.snd a)) (F.map j) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace e₂.inv
  have hrange : IsCompact
      (Set.range (Limits.pullback.fst (F.map (hc.rep.snd a)) (F.map j))) :=
    isCompact_range (Limits.pullback.fst (F.map (hc.rep.snd a)) (F.map j)).continuous
  change IsCompact (Set.range (Limits.pullback.fst (F.map (hc.rep.snd a)) O.ι)) at hrange
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι] at hrange
  exact hrange

/-- The restriction of a morphism of the site to an open of its source landing in a
prescribed open of its target. -/
private noncomputable def liftOpensObject {E A : BigFppfOver B S hS} (p : E ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj E).Opens)
    (P : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (h : O ≤ ((BigFppfOver.toScheme B S hS).map p) ⁻¹ᵁ P) :
    opensObject B S hS E O ⟶ opensObject B S hS A P :=
  Over.homMk (ObjectProperty.homMk
    (((BigFppfOver.toScheme B S hS).map p).resLE P O h)) (by
      apply B.inclusion.map_injective
      change (((BigFppfOver.toScheme B S hS).map p).resLE P O h) ≫
          (P.ι ≫ B.inclusion.map A.hom) = O.ι ≫ B.inclusion.map E.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg (O.ι ≫ ·) (congrArg B.inclusion.map p.w))

/-- The restriction of a morphism of the site to opens commutes with the two inclusions. -/
private lemma liftOpensObject_fac {E A : BigFppfOver B S hS} (p : E ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj E).Opens)
    (P : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (h : O ≤ ((BigFppfOver.toScheme B S hS).map p) ⁻¹ᵁ P) :
    liftOpensObject B S hS p O P h ≫ opensObjectι B S hS A P =
      opensObjectι B S hS E O ≫ p :=
  (BigFppfOver.toScheme B S hS).map_injective (Scheme.Hom.resLE_comp_ι _ _)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-- The source of a cartesian square of schemes has as image the preimage of the image of the
opposite side. -/
private lemma range_fst_of_isPullback
    {R W T U : Scheme.{u}} {r : R ⟶ W} {s : R ⟶ T} {p : W ⟶ U} {j : T ⟶ U}
    (h : IsPullback r s p j) : Set.range r = p ⁻¹' Set.range j := by
  rw [← h.isoPullback_hom_fst]
  show Set.range ((Limits.pullback.fst p j) ∘ h.isoPullback.hom) = _
  rw [(show Function.Surjective h.isoPullback.hom from
    (inferInstance : Surjective h.isoPullback.hom).surj).range_comp]
  exact Scheme.Pullback.range_fst p j

/-- Compactness of a preimage may be checked on a finite family of continuous maps whose
images cover the source. -/
private lemma isCompact_preimage_of_finite_cover
    {I : Type*} [Finite I] {W T : Type*} {R : I → Type*} [TopologicalSpace W]
    [∀ i, TopologicalSpace (R i)] (p : W → T)
    (r : ∀ i, R i → W) (hr : ∀ i, Continuous (r i))
    (hcover : ∀ w : W, ∃ i, w ∈ Set.range (r i))
    (O : Set T) (hqc : ∀ i, IsCompact ((p ∘ r i) ⁻¹' O)) :
    IsCompact (p ⁻¹' O) := by
  have heq : p ⁻¹' O = ⋃ i, r i '' ((p ∘ r i) ⁻¹' O) := by
    ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · obtain ⟨i, x, rfl⟩ := hcover w
      exact Set.mem_iUnion.mpr ⟨i, x, hw, rfl⟩
    · obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hw
      exact hx
  rw [heq]
  exact isCompact_iUnion fun i => (hqc i).image (hr i)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-compactness of a representable morphism of presheaves may be checked on a finite
family of morphisms of the site whose images cover its source. -/
private lemma presheafQuasiCompact_of_finite_source_cover
    {U : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    {I : Type*} [Finite I] (T : I → BigFppfOver B S hS)
    (j : ∀ i, T i ⟶ U)
    (hcover : ∀ u : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, u ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)))
    (hqc : ∀ i, (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (j i) ≫ f)) :
    (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  let F := BigFppfOver.toScheme B S hS
  have _ : MorphismProperty.RespectsIso (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    quasiCompact_isStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      F).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd
    (P := MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) F)
    hf ?_
  intro V g
  set p := hf.fst' g with hp
  set q := hf.snd g with hq
  set s : ∀ i, (hqc i).rep.pullback g ⟶ T i := fun i => (hqc i).rep.fst' g with hs
  set t : ∀ i, (hqc i).rep.pullback g ⟶ V := fun i => (hqc i).rep.snd g with ht
  set l : ∀ i, (hqc i).rep.pullback g ⟶ hf.pullback g := fun i =>
    hf.lift (yoneda.map (s i ≫ j i)) (t i) (by
      simpa only [Functor.map_comp, Category.assoc] using ((hqc i).rep.isPullback' g).w) with hl
  have hlp (i) : l i ≫ p = s i ≫ j i := yoneda.map_injective <| by
    rw [Functor.map_comp, hp, hf.map_fst']
    exact hf.lift_fst (g := g) (yoneda.map (s i ≫ j i)) (t i) _
  have hlq (i) : l i ≫ q = t i := hf.lift_snd _ _ _
  have hcart (i) : IsPullback (l i) (s i) p (j i) := by
    apply IsPullback.of_map_of_faithful yoneda
    apply IsPullback.flip
    have hW : IsPullback (yoneda.map p) (yoneda.map q) f g := hf.isPullback' g
    apply (hW.paste_vert_iff (by simp only [← Functor.map_comp, hlp])).mp
    simpa only [← Functor.map_comp, hlq] using (hqc i).rep.isPullback' g
  refine ⟨fun O ho hc => ?_⟩
  refine isCompact_preimage_of_finite_cover (F.map q).base (fun i => (F.map (l i)).base)
    (fun i => (F.map (l i)).continuous) ?_ O ?_
  · intro w
    obtain ⟨i, hi⟩ := hcover (F.map p w)
    exact ⟨i, by rwa [range_fst_of_isPullback ((hcart i).map F)]⟩
  · intro i
    show IsCompact ((F.map (l i) ≫ F.map q) ⁻¹' O)
    rw [← Functor.map_comp, hlq]
    have _ : QuasiCompact (F.map (t i)) := (hqc i).property_snd g
    exact QuasiCompact.isCompact_preimage (f := F.map (t i)) O ho hc

/-- If every affine étale chart of an algebraic space is quasi-compact, then so is every
morphism to it from an object with quasi-compact underlying scheme. -/
private lemma presheafQuasiCompact_of_affine_etale_charts
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hcharts : ∀ (A : BigFppfOver B S hS)
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
      (a : yoneda.obj A ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X)
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  classical
  let F := BigFppfOver.toScheme B S hS
  let Pe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F
  let Pq := MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) F
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : Pe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : Pq.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : Pe.IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  have _ : Pq.IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  obtain ⟨A, a, hsurj, ha⟩ := hX.exists_atlas
  set p := ha.rep.fst' f with hpdef
  set t := ha.rep.snd f with htdef
  have ht : Etale (F.map t) := ha.property_snd f
  have htsurj : Surjective (F.map t) := hsurj.property f _ _ (ha.rep.isPullback f)
  have hex (e : F.obj (ha.rep.pullback f)) :
      ∃ (P : (F.obj A).Opens) (O : (F.obj (ha.rep.pullback f)).Opens),
      IsAffineOpen P ∧ IsAffineOpen O ∧ e ∈ O ∧ O ≤ (F.map p) ⁻¹ᵁ P := by
    obtain ⟨P, hP, heP, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := F.obj A) (U := ⊤) (x := F.map p e) (by trivial)
    obtain ⟨O, hO, heO, hOP⟩ := exists_isAffineOpen_mem_and_subset
      (U := (F.map p) ⁻¹ᵁ P) heP
    exact ⟨P, O, hP, hO, heO, hOP⟩
  choose P O hP hO heO hOP using hex
  set j : ∀ e, opensObject B S hS (ha.rep.pullback f) (O e) ⟶ U := fun e =>
    opensObjectι B S hS (ha.rep.pullback f) (O e) ≫ t with hjdef
  have hje (e) : Etale (F.map (j e)) := by
    show Etale ((O e).ι ≫ F.map t)
    infer_instance
  have hopen (e) : IsOpen (Set.range (F.map (j e))) :=
    (F.map (j e)).isOpenMap.isOpen_range
  have hcover : (Set.univ : Set (F.obj U)) ⊆
      ⋃ e : F.obj (ha.rep.pullback f), Set.range (F.map (j e)) := by
    intro u _
    obtain ⟨e, he⟩ := htsurj.surj u
    exact Set.mem_iUnion.mpr ⟨e, ⟨e, heO e⟩, he⟩
  obtain ⟨K, hK⟩ := isCompact_univ.elim_finite_subcover
    (fun e : F.obj (ha.rep.pullback f) => Set.range (F.map (j e))) hopen hcover
  have hf : yoneda.relativelyRepresentable f :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS hX f
  refine presheafQuasiCompact_of_finite_source_cover B S hS f hf
    (fun e : K => opensObject B S hS (ha.rep.pullback f) (O e)) (fun e : K => j e) ?_ ?_
  · intro u
    obtain ⟨e, heK, he⟩ := Set.mem_iUnion₂.mp (hK (Set.mem_univ u))
    exact ⟨⟨e, heK⟩, he⟩
  · intro e
    set ai := opensObjectι B S hS A (P e) with haidef
    set b := liftOpensObject B S hS p (O e) (P e) (hOP e) with hbdef
    have hai : Pe.presheaf (yoneda.map ai) :=
      MorphismProperty.relative_map (show Etale (F.map ai) from by
        show Etale (P e).ι
        infer_instance)
    have hchart : Pq.presheaf (yoneda.map ai ≫ a) :=
      hcharts (opensObject B S hS A (P e)) (hP e) _
        (MorphismProperty.comp_mem Pe.presheaf _ _ hai ha)
    have hb : Pq.presheaf (yoneda.map b) := by
      refine MorphismProperty.relative_map (show QuasiCompact (F.map b) from ?_)
      have _ : IsAffine (F.obj (opensObject B S hS (ha.rep.pullback f) (O e))) := hO e
      have _ : IsAffine (F.obj (opensObject B S hS A (P e))) := hP e
      infer_instance
    have hfac : yoneda.map (j e) ≫ f = yoneda.map b ≫ (yoneda.map ai ≫ a) := by
      rw [← Category.assoc, ← Functor.map_comp]
      show yoneda.map (opensObjectι B S hS (ha.rep.pullback f) (O e) ≫ t) ≫ f =
        yoneda.map (liftOpensObject B S hS p (O e) (P e) (hOP e) ≫
          opensObjectι B S hS A (P e)) ≫ a
      rw [liftOpensObject_fac, Functor.map_comp, Functor.map_comp, Category.assoc,
        Category.assoc, (ha.rep.isPullback' f).w]
    rw [hfac]
    exact MorphismProperty.comp_mem Pq.presheaf _ _ hb hchart

/-- A locally Noetherian decent algebraic space is quasi-separated. -/
@[stacks 0BB6]
theorem isAbsolutelyQuasiSeparated_of_isLocallyNoetherian_of_isDecentSpace
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (hdec : IsDecentSpace B S hS X) :
    IsAbsolutelyQuasiSeparated B S hS hZ X := by
  obtain ⟨A, a, hasurj, haetale, hAN⟩ := hNoeth
  have hcharts : ∀ (C : BigFppfOver B S hS)
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj C))
      (c : yoneda.obj C ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c := fun C hC c hc =>
    presheafQuasiCompact_of_affine_etale_chart B S hS hX hdec hasurj haetale hAN hC hc
  refine (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS hZ X hX).mpr ?_
  intro U V f g hU hV
  have hf := presheafQuasiCompact_of_affine_etale_charts B S hS hX hcharts U f inferInstance
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hf.rep.snd g)) :=
    hf.property_snd g
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := inferInstance
  exact ⟨hf.rep.pullback g, QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map (hf.rep.snd g)),
    ⟨(hf.rep.isPullback g).isoPullback⟩⟩

end AlgebraicGeometry.Space

end
