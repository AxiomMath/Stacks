module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.SpreadOutPreliminaries
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.ConnectedFibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ConditionalStatements

/-!
# Spreading out a geometrically connected open in a fibre

Let `f : X ⟶ S` be flat and of finite presentation with geometrically reduced fibres, and let
`T` be an open subscheme of the fibre of `f` over a point `s` which is geometrically connected
over the residue field of `s`. Then, after an affine elementary étale neighbourhood of `s`, the
open `T` spreads to a quasi-compact open of the base change all of whose fibres are
geometrically connected.

This is Stacks Tag 055W. It is proved here from Tag 0570 and Tag 057I, which are carried as the
explicit hypotheses `AlgebraicGeometry.Statement0570` and `AlgebraicGeometry.Statement057I`.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_open_geometricallyConnected` is Tag
  055W, with the statements of Tag 0570 and Tag 057I as explicit hypotheses.
* `AlgebraicGeometry.statement055W_of_statement0570_statement057I` records that this has exactly
  the binders of `AlgebraicGeometry.Statement055W`, so that it discharges the hypothesis of
  `AlgebraicGeometry.statement057J_of_statement055W`.
* `AlgebraicGeometry.statement055W_of_statement0570_statement055P_statement055R` is the same
  result with Tag 057I replaced by the two inputs Tags 055P and 055R from which it is proved.

## Implementation notes

The argument follows the Stacks Project. A point `y` of `T` is chosen which is closed in the
fibre and at which `f` is Cohen–Macaulay; Tag 0570 produces a quasi-finite flat slice `Z ⟶ X`
through `y` whose fibre over `s` is the single point `z`. Tag 02LK makes `Z` finite over an
elementary étale neighbourhood of `s` after shrinking, which exhibits a finite locally free
multisection of the base change of `f`; Tag 057I then spreads the geometric connectedness of
the fibre to a quasi-compact open.

Two shrinkings of the base are needed before Tag 057I applies: one to make the neighbourhood
affine, and one to confine the finite part of `Z` to the open of the base change lying over the
chosen quasi-compact open `W` of `X` which cuts out `T`. A third shrinking, to the affine open
`A` of the image of the open produced by Tag 057I, makes every fibre of the final open nonempty,
which is what turns the fibrewise conclusion of Tag 057I into geometric connectedness of the
structure morphism.

Since Tag 0570 and Tag 057I are not available unconditionally, the two theorems are left
untagged.

## References

* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms
  AlgebraicGeometry.ConnectedComponentSection

universe u

namespace AlgebraicGeometry

/-- The fibre product of compact schemes over a quasi-separated base is compact. -/
private theorem compactSpace_pullback_of_compactSpace {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Z] :
    CompactSpace ↑(pullback f g) := by
  have := AlgebraicGeometry.quasiCompact_of_compactSpace f
  infer_instance

/-- **Stacks Project, Tag 055W, conditional on Tags 0570 and 057I.** A geometrically connected
open in a fibre of a flat, finitely presented morphism with geometrically reduced fibres
spreads, after an affine elementary étale base change, to a quasi-compact open with
geometrically connected fibres. -/
theorem exists_elementaryEtaleNeighborhood_open_geometricallyConnected
    (h0570 : Statement0570.{u}) (h057I : Statement057I.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (T : (f.fiber s).Opens)
    (hfp : FinitePresentation f) [Flat f] [GeometricallyReduced f]
    [GeometricallyConnected (T.ι ≫ f.fiberToSpecResidueField s)] :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary) (_ : IsAffine U.scheme)
      (V : (pullback f U.toBase).Opens),
      QuasiCompact V.ι ∧ GeometricallyConnected (V.ι ≫ pullback.snd f U.toBase) ∧
      ∀ x : (pullback.snd f U.toBase).fiber U.point,
        ((pullback.snd f U.toBase).fiberι U.point x ∈ V) ↔
          pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point x) ∈
            f.fiberι s '' (T : Set (f.fiber s)) := by
  let : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  let : QuasiCompact f := hfp.quasiCompact
  obtain ⟨Saff, hSaffAffine, hsaff, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : S.Opens)) (by simp)
  have hTset : (T : Set (f.fiber s)).Nonempty := by
    let : Surjective (T.ι ≫ f.fiberToSpecResidueField s) := inferInstance
    obtain ⟨x, -⟩ := (T.ι ≫ f.fiberToSpecResidueField s).surjective
      (IsLocalRing.closedPoint (S.residueField s))
    exact ⟨x.1, x.2⟩
  obtain ⟨W, hWcompact, hWfiber, hWbase⟩ :=
    exists_isCompact_opens_preimage_fiber_eq f s T Saff hsaff
  obtain ⟨y, hyT, hyclosed, hyCM⟩ := exists_closed_cohenMacaulay_point_mem_opens f s T hTset
  have hWT (t : f.fiber s) : f.fiberι s t ∈ W ↔ t ∈ T := by
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (x := t), ← hWfiber]; rfl
  let x : X := f.fiberι s y
  have hfx : f x = s := (f.fiberHomeo s y).2
  have hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
    have hyclosed' : IsClosed ({y} : Set (f.fiber s)) := mem_closedPoints_iff.mp hyclosed
    have hs : f ⁻¹' {s} = f ⁻¹' {f x} := by ext w; simp [hfx]
    let e : f.fiber s ≃ₜ f.fiber (f x) :=
      (f.fiberHomeo s).trans ((Homeomorph.setCongr hs).trans (f.fiberHomeo (f x)).symm)
    have heq : e y = f.asFiber x := by
      apply (f.fiberι (f x)).isEmbedding.injective
      simp [e, x, Homeomorph.setCongr, Scheme.Hom.fiberHomeo_apply,
        Scheme.Hom.fiberι_fiberHomeo_symm, Scheme.Hom.fiberι_asFiber]
    have hclosed' : IsClosed (e '' ({y} : Set (f.fiber s))) := e.isClosedMap _ hyclosed'
    rw [Set.image_singleton] at hclosed'
    simpa [heq] using hclosed'
  obtain ⟨Z, i, z, hi, hiz, hreg, hflat, hfpz, hqf, hfiber⟩ := h0570 f x ⟨_, hyCM⟩ hclosed
  let g : Z ⟶ S := i ≫ f
  have hgx : g z = f x := by simpa [g] using congrArg f hiz
  have hgs : g z = s := hgx.trans hfx
  have hzg : IsIsolatedPoint (g.asFiber z) := by
    rw [isIsolatedPoint_iff]
    have hpoint (w : g.fiber (g z)) : w = g.asFiber z := by
      apply (g.fiberι (g z)).isEmbedding.injective
      have hz' : g.fiberι (g z) w = z := by
        have hmem : g.fiberι (g z) w ∈ {z' : Z | g z' = f x} :=
          ((g.fiberHomeo (g z) w).2).trans hgx
        rw [hfiber] at hmem
        simpa using hmem
      simp [hz', Scheme.Hom.fiberι_asFiber]
    have htop : ({g.asFiber z} : Set (g.fiber (g z))) = Set.univ := by
      ext w
      simp [hpoint w]
    rw [htop]
    exact isOpen_univ
  let : LocallyOfFinitePresentation g := hfpz
  let : LocallyOfFiniteType g := inferInstance
  let fin := Classical.choice (Stacks.Flatness.exists_etaleNeighborhood_finiteAt g z hzg)
  obtain ⟨Uaff, jaff, hUaff, hUaffAffine, hjaff, hjaffBase, hjaffPoint⟩ :=
    exists_isAffine_elementary_refinement fin.neighborhood fin.elementary
  let Urel : EtaleNeighborhood fin.neighborhood.scheme fin.neighborhood.point :=
    { scheme := Uaff.scheme
      point := Uaff.point
      toBase := jaff
      map_point := hjaffPoint }
  have hUrel : Urel.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    change IsIso (jaff.residueFieldMap Uaff.point)
    infer_instance
  let Ufinal : EtaleNeighborhood S s :=
    { scheme := Uaff.scheme
      point := Uaff.point
      toBase := jaff ≫ fin.neighborhood.toBase
      map_point := by
        rw [Scheme.Hom.comp_apply, hjaffPoint]
        exact fin.neighborhood.map_point.trans hgs }
  let Naff : EtaleNeighborhood S (g z) :=
    { scheme := Uaff.scheme
      point := Uaff.point
      toBase := jaff ≫ fin.neighborhood.toBase
      map_point := by
        rw [Scheme.Hom.comp_apply, hjaffPoint]
        exact fin.neighborhood.map_point }
  have hNpoint : IsIso (fin.neighborhood.toBase.residueFieldMap (jaff Uaff.point)) := by
    rw [hjaffPoint]
    exact (fin.neighborhood.isElementary_iff).mp fin.elementary
  have hNaffbase : IsIso (Naff.toBase.residueFieldMap Naff.point) :=
    isIso_residueFieldMap_comp jaff fin.neighborhood.toBase Uaff.point inferInstance hNpoint
  have hNaff : Naff.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact hNaffbase
  have hUfinal : Ufinal.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact hNaffbase
  have hfiniteNaff : Stacks.Flatness.IsFiniteNeighborhoodAt g z Naff
      (pullback.map g (jaff ≫ fin.neighborhood.toBase) g fin.neighborhood.toBase
        (𝟙 Z) jaff (𝟙 S) (by simp) (by simp) ⁻¹ᵁ fin.openSubscheme) :=
    Stacks.Flatness.isFiniteNeighborhoodAt_baseChange g z fin.neighborhood fin.openSubscheme
      fin.spec Urel hUrel
  let Yg := pullback g Ufinal.toBase
  let mzg : Yg ⟶ pullback g fin.neighborhood.toBase :=
    pullback.map g (jaff ≫ fin.neighborhood.toBase) g fin.neighborhood.toBase
      (𝟙 Z) jaff (𝟙 S) (by simp) (by simp)
  let F : Yg.Opens := mzg ⁻¹ᵁ fin.openSubscheme
  have hFspec : Stacks.Flatness.IsFiniteNeighborhoodAt g z Naff F := hfiniteNaff
  obtain ⟨hFfinite, ⟨v, hv, hvuniq⟩, hFpoint⟩ := hFspec
  have hvX : (pullback.fst g Ufinal.toBase) (F.ι v) = z := (hFpoint v hv).1
  let Yf := pullback f Ufinal.toBase
  let mf : Yg ⟶ Yf :=
    pullback.map g Ufinal.toBase f Ufinal.toBase i (𝟙 Ufinal.scheme) (𝟙 S)
      (by simp [g]) (by simp)
  let B : Yf.Opens := (pullback.fst f Ufinal.toBase) ⁻¹ᵁ W
  have hmfFst : mf ≫ pullback.fst f Ufinal.toBase = pullback.fst g Ufinal.toBase ≫ i :=
    pullback.lift_fst _ _ _
  have hmfpoint : pullback.fst f Ufinal.toBase (mf (F.ι v)) = x := by
    calc
      pullback.fst f Ufinal.toBase (mf (F.ι v)) =
          (mf ≫ pullback.fst f Ufinal.toBase) (F.ι v) := by simp
      _ = (pullback.fst g Ufinal.toBase ≫ i) (F.ι v) := by rw [hmfFst]
      _ = i (pullback.fst g Ufinal.toBase (F.ι v)) := by simp
      _ = i z := by rw [hvX]
      _ = x := hiz
  have hyW : (f.fiberι s y) ∈ W := (hWT y).2 hyT
  have hvB : mf (F.ι v) ∈ B := by
    change pullback.fst f Ufinal.toBase (mf (F.ι v)) ∈ W
    rw [hmfpoint]
    exact hyW
  let qF : F.toScheme ⟶ Uaff.scheme := F.ι ≫ pullback.snd g Ufinal.toBase
  let : IsFinite qF := hFfinite
  have hqFclosed : IsClosedMap qF := Scheme.Hom.isClosedMap qF
  let C : Set F := {w | mf (F.ι w) ∉ B}
  have hCclosed : IsClosed C := by
    have hopen : IsOpen {w : F | mf (F.ι w) ∈ B} := B.2.preimage (F.ι ≫ mf).continuous
    exact hopen.isClosed_compl
  let D : Uaff.scheme.Opens := ⟨(qF '' C)ᶜ, (hqFclosed C hCclosed).isOpen_compl⟩
  have hDpoint : Uaff.point ∈ D := by
    intro hbad
    obtain ⟨w, hwC, hwq⟩ := hbad
    have hwv : w = v := hvuniq w hwq
    subst hwv
    exact hwC hvB
  have hFmapsB (w : F) (hwD : qF w ∈ D) : mf (F.ι w) ∈ B := by
    by_contra hwB
    exact hwD ⟨w, hwB, rfl⟩
  let D₀ : Naff.scheme.Opens := D ⊓ Naff.toBase ⁻¹ᵁ Saff
  have hD₀point : Naff.point ∈ D₀ := by
    refine ⟨hDpoint, ?_⟩
    change Naff.toBase Naff.point ∈ Saff
    rw [Naff.map_point, hgs]
    exact hsaff
  obtain ⟨A, hAaff, hApoint, hAsub⟩ := exists_isAffineOpen_mem_and_subset (U := D₀) hD₀point
  have hAres : ∀ p : A.toScheme, IsIso (A.ι.residueFieldMap p) := fun p => inferInstance
  let Urel1 : EtaleNeighborhood Naff.scheme Naff.point :=
    { scheme := A.toScheme
      point := ⟨Naff.point, hApoint⟩
      toBase := A.ι
      map_point := rfl }
  have hUrel1 : Urel1.IsElementary :=
    EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion A.ι ⟨Naff.point, hApoint⟩
  let U1 : EtaleNeighborhood S s :=
    { scheme := A.toScheme
      point := ⟨Naff.point, hApoint⟩
      toBase := A.ι ≫ Naff.toBase
      map_point := Naff.map_point.trans hgs }
  have hU1 : U1.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact isIso_residueFieldMap_comp A.ι Naff.toBase ⟨Naff.point, hApoint⟩ (hAres _) hNaffbase
  have hU1aff : IsAffine U1.scheme := hAaff
  let u0 : U1.scheme ⟶ Saff.toScheme :=
    IsOpenImmersion.lift Saff.ι U1.toBase (by
      rintro w ⟨p, rfl⟩
      exact ⟨⟨Naff.toBase (A.ι p), (hAsub p.2).2⟩, rfl⟩)
  have hu0 : u0 ≫ Saff.ι = U1.toBase := IsOpenImmersion.lift_fac _ _ _
  let w0 : W.toScheme ⟶ Saff.toScheme :=
    IsOpenImmersion.lift Saff.ι (W.ι ≫ f) (by
      rintro w ⟨p, rfl⟩
      exact ⟨⟨f (W.ι p), hWbase p.2⟩, rfl⟩)
  have hw0 : w0 ≫ Saff.ι = W.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hfinite1 :=
    Stacks.Flatness.isFiniteNeighborhoodAt_baseChange g z Naff F hfiniteNaff Urel1 hUrel1
  let Yg1 := pullback g U1.toBase
  let md : Yg1 ⟶ pullback g Naff.toBase :=
    pullback.map g U1.toBase g Naff.toBase (𝟙 Z) A.ι (𝟙 S) (by simp) (by simp [U1])
  let F1 : Yg1.Opens := md ⁻¹ᵁ F
  have hF1finite : IsFinite (F1.ι ≫ pullback.snd g U1.toBase) := hfinite1.1
  let Yf1 := pullback f U1.toBase
  let m1f : Yg1 ⟶ Yf1 :=
    pullback.map g U1.toBase f U1.toBase i (𝟙 U1.scheme) (𝟙 S)
      (by simp [g]) (by simp)
  let B1 : Yf1.Opens := (pullback.fst f U1.toBase) ⁻¹ᵁ W
  let q1 : F1.toScheme ⟶ U1.scheme := F1.ι ≫ pullback.snd g U1.toBase
  let fB : B1.toScheme ⟶ U1.scheme := B1.ι ≫ pullback.snd f U1.toBase
  let : Flat g := hflat
  let : QuasiSeparated f := hfp.quasiSeparated
  let : IsFinite q1 := hF1finite
  have hq1FLF : IsFiniteLocallyFree q1 :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation q1).mpr
      ⟨hF1finite, inferInstance, inferInstance⟩
  let : IsFiniteLocallyFree q1 := hq1FLF
  let : Flat fB := inferInstance
  let : LocallyOfFinitePresentation fB := inferInstance
  -- Compactness of `B1` is proved over the affine open `Saff`: the morphism `U1.toBase` need
  -- not be quasi-compact over an arbitrary scheme `S`.
  let P := pullback W.ι (pullback.fst f U1.toBase)
  let kP : P ⟶ Yf1 := pullback.snd W.ι (pullback.fst f U1.toBase)
  let R := pullback Saff.ι U1.toBase
  let lR : U1.scheme ⟶ R := pullback.lift u0 (𝟙 U1.scheme) (by rw [hu0]; simp)
  have hlRright : lR ≫ pullback.snd Saff.ι U1.toBase = 𝟙 U1.scheme := pullback.lift_snd _ _ _
  have hlRleft : pullback.snd Saff.ι U1.toBase ≫ lR = 𝟙 R := by
    apply pullback.hom_ext
    · apply (cancel_mono Saff.ι).1
      calc
        ((pullback.snd Saff.ι U1.toBase ≫ lR) ≫ pullback.fst Saff.ι U1.toBase) ≫ Saff.ι =
            pullback.snd Saff.ι U1.toBase ≫ (u0 ≫ Saff.ι) := by
              simp only [Category.assoc, lR, pullback.lift_fst]
        _ = pullback.snd Saff.ι U1.toBase ≫ U1.toBase := by rw [hu0]
        _ = pullback.fst Saff.ι U1.toBase ≫ Saff.ι := by rw [pullback.condition]
        _ = ((𝟙 R) ≫ pullback.fst Saff.ι U1.toBase) ≫ Saff.ι := by simp
    · rw [Category.assoc, hlRright, Category.comp_id, Category.id_comp]
  let eR : U1.scheme ≅ R := ⟨lR, pullback.snd Saff.ι U1.toBase, hlRright, hlRleft⟩
  let : IsIso eR.hom := eR.isIso_hom
  have hmQ1 : w0 ≫ 𝟙 Saff.toScheme = 𝟙 W.toScheme ≫ w0 := by simp
  have hmQ2 : u0 ≫ 𝟙 Saff.toScheme = eR.hom ≫ pullback.fst Saff.ι U1.toBase := by
    rw [Category.comp_id]
    exact (pullback.lift_fst u0 (𝟙 U1.scheme) _).symm
  let mQ : pullback w0 u0 ⟶ pullback w0 (pullback.fst Saff.ι U1.toBase) :=
    pullback.map w0 u0 w0 (pullback.fst Saff.ι U1.toBase)
      (𝟙 W.toScheme) eR.hom (𝟙 Saff.toScheme) hmQ1 hmQ2
  let : IsIso mQ :=
    pullback.map_isIso w0 u0 w0 (pullback.fst Saff.ι U1.toBase)
      (𝟙 W.toScheme) eR.hom (𝟙 Saff.toScheme) hmQ1 hmQ2
  let e1 : P ≅ pullback (W.ι ≫ f) U1.toBase := pullbackRightPullbackFstIso f U1.toBase W.ι
  let e2 : pullback w0 (pullback.fst Saff.ι U1.toBase) ≅ pullback (W.ι ≫ f) U1.toBase := by
    simpa only [hw0] using (pullbackRightPullbackFstIso Saff.ι U1.toBase w0)
  let eP : P ≅ pullback w0 u0 := e1.trans (e2.symm.trans (asIso mQ).symm)
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hWcompact
  let : IsAffine Saff.toScheme := hSaffAffine
  let : CompactSpace ↥(pullback w0 u0) := compactSpace_pullback_of_compactSpace w0 u0
  let : CompactSpace P := eP.inv.homeomorph.compactSpace
  have hkPrange : Set.range kP = (B1 : Set Yf1) := by
    rw [← Scheme.Hom.coe_opensRange]
    simp [kP, B1, Scheme.Hom.opensRange_pullbackSnd]
  have hBcompact : IsCompact (B1 : Set Yf1) := by
    rw [← hkPrange]
    simpa [Set.image_univ] using (isCompact_univ (X := P)).image kP.continuous
  let : CompactSpace B1.toScheme := isCompact_iff_compactSpace.mp hBcompact
  let : QuasiSeparatedSpace U1.scheme := by infer_instance
  let : QuasiCompact fB := inferInstance
  let : QuasiSeparated fB := inferInstance
  have hfBfp : FinitePresentation fB := ⟨inferInstance, inferInstance, inferInstance⟩
  let : GeometricallyReduced fB := geometricallyReduced_comp_opens
    (pullback.snd f U1.toBase) B1
  have hredB : ∀ a : U1.scheme, GeometricallyReduced (fB.fiberToSpecResidueField a) :=
    fun _ => inferInstance
  have hm1fFst : m1f ≫ pullback.fst f U1.toBase = pullback.fst g U1.toBase ≫ i :=
    pullback.lift_fst _ _ _
  have hsectionBase : ∀ w : F1, (pullback.fst f U1.toBase) (m1f (F1.ι w)) ∈ W := by
    intro w
    let wold : F := ⟨md (F1.ι w), w.2⟩
    have hsnd : md ≫ pullback.snd g Naff.toBase = pullback.snd g U1.toBase ≫ A.ι :=
      pullback.lift_snd _ _ _
    have hbase : qF wold = A.ι ((pullback.snd g U1.toBase) (F1.ι w)) := by
      calc
        qF wold = (md ≫ pullback.snd g Naff.toBase) (F1.ι w) := rfl
        _ = (pullback.snd g U1.toBase ≫ A.ι) (F1.ι w) := by rw [hsnd]
        _ = A.ι ((pullback.snd g U1.toBase) (F1.ι w)) := by simp
    have hD : qF wold ∈ D := by
      rw [hbase]
      exact (hAsub ((pullback.snd g U1.toBase) (F1.ι w)).2).1
    have hB := hFmapsB wold hD
    have hfstmd : md ≫ pullback.fst g Naff.toBase = pullback.fst g U1.toBase :=
      pullback.lift_fst _ _ _
    have hX : pullback.fst g U1.toBase (F1.ι w) =
        pullback.fst g Ufinal.toBase (md (F1.ι w)) := by
      calc
        pullback.fst g U1.toBase (F1.ι w) =
            (md ≫ pullback.fst g Naff.toBase) (F1.ι w) := by rw [← hfstmd]
        _ = pullback.fst g Ufinal.toBase (md (F1.ι w)) := by simp [Ufinal, Naff]
    have hcoord : pullback.fst f U1.toBase (m1f (F1.ι w)) =
        pullback.fst f Ufinal.toBase (mf (F.ι wold)) := by
      calc
        pullback.fst f U1.toBase (m1f (F1.ι w)) =
            (pullback.fst g U1.toBase ≫ i) (F1.ι w) := by
              rw [← Scheme.Hom.comp_apply, hm1fFst]
        _ = (pullback.fst g Ufinal.toBase ≫ i) (F.ι wold) := congrArg i hX
        _ = (mf ≫ pullback.fst f Ufinal.toBase) (F.ι wold) := by rw [hmfFst]
        _ = pullback.fst f Ufinal.toBase (mf (F.ι wold)) := by simp
    change pullback.fst f U1.toBase (m1f (F1.ι w)) ∈ W
    rw [hcoord]
    exact hB
  have hrangeσ : Set.range (F1.ι ≫ m1f) ⊆ Set.range B1.ι := by
    rintro q ⟨w, rfl⟩
    rw [B1.range_ι]
    exact hsectionBase w
  let σ1 : F1.toScheme ⟶ B1.toScheme := IsOpenImmersion.lift B1.ι (F1.ι ≫ m1f) hrangeσ
  have hσ1 : σ1 ≫ B1.ι = F1.ι ≫ m1f := IsOpenImmersion.lift_fac _ _ _
  have hσ : σ1 ≫ fB = q1 := by
    have hm1snd : m1f ≫ pullback.snd f U1.toBase = pullback.snd g U1.toBase :=
      pullback.lift_snd _ _ _
    change σ1 ≫ B1.ι ≫ pullback.snd f U1.toBase = F1.ι ≫ pullback.snd g U1.toBase
    rw [← Category.assoc, hσ1, Category.assoc, hm1snd]
  have hZ1 : Nonempty (q1.fiber U1.point) := by
    obtain ⟨v1, hv1, -⟩ := hfinite1.2.1
    exact ⟨(q1.fiberHomeo U1.point).symm ⟨v1, hv1⟩⟩
  have hconnB1 : GeometricallyConnected (fB.fiberToSpecResidueField U1.point) := by
    let : IsIso U1.residueFieldMap := hU1
    let pB := fiberMapOfSourceHom B1.ι (pullback.snd f U1.toBase) U1.point
    let r : fB.fiber U1.point ⟶ f.fiber s := pB ≫ (elementaryFiberIso f U1).hom
    have hpBfiberι : ∀ w : fB.fiber U1.point,
        (pullback.snd f U1.toBase).fiberι U1.point (pB w) = B1.ι (fB.fiberι U1.point w) :=
      fun w => congrArg (fun k : fB.fiber U1.point ⟶ Yf1 => k w)
        (fiberMapOfSourceHom_fiberι B1.ι (pullback.snd f U1.toBase) U1.point)
    have hrfiberι : ∀ w : (pullback.snd f U1.toBase).fiber U1.point,
        f.fiberι s ((elementaryFiberIso f U1).hom w) =
          pullback.fst f U1.toBase ((pullback.snd f U1.toBase).fiberι U1.point w) :=
      fun w => congrArg (fun k : (pullback.snd f U1.toBase).fiber U1.point ⟶ X => k w)
        (elementaryFiberIso_hom_fiberι f U1)
    have hrOpen : IsOpenImmersion r := by
      have hpB : IsOpenImmersion pB :=
        MorphismProperty.of_isPullback
          (fiberMapOfSourceHom_isPullback B1.ι (pullback.snd f U1.toBase) U1.point).flip
          inferInstance
      exact IsOpenImmersion.comp _ _
    have hrange : Set.range r = (T : Set (f.fiber s)) := by
      apply Set.Subset.antisymm
      · rintro w ⟨w', rfl⟩
        have hW : pullback.fst f U1.toBase
            ((pullback.snd f U1.toBase).fiberι U1.point (pB w')) ∈ W := by
          rw [hpBfiberι w']
          exact (fB.fiberι U1.point w').property
        refine (hWT _).1 ?_
        rw [show f.fiberι s (r w') = pullback.fst f U1.toBase
          ((pullback.snd f U1.toBase).fiberι U1.point (pB w')) from hrfiberι (pB w')]
        exact hW
      · intro w hw
        let w' : (pullback.snd f U1.toBase).fiber U1.point := (elementaryFiberIso f U1).inv w
        have hw' : (elementaryFiberIso f U1).hom w' = w := by
          change ((elementaryFiberIso f U1).inv ≫ (elementaryFiberIso f U1).hom) w = w
          rw [Iso.inv_hom_id]
          rfl
        have hW : pullback.fst f U1.toBase
            ((pullback.snd f U1.toBase).fiberι U1.point w') ∈ W := by
          rw [← hrfiberι w', hw']
          exact (hWT w).2 hw
        let b : B1.toScheme := ⟨(pullback.snd f U1.toBase).fiberι U1.point w', hW⟩
        have hb : fB b = U1.point :=
          ((pullback.snd f U1.toBase).fiberHomeo U1.point w').property
        let w'' : fB.fiber U1.point := (fB.fiberHomeo U1.point).symm ⟨b, hb⟩
        have hp : pB w'' = w' := by
          apply ((pullback.snd f U1.toBase).fiberι U1.point).isEmbedding.injective
          rw [hpBfiberι w'']
          change B1.ι (fB.fiberι U1.point w'') =
            (pullback.snd f U1.toBase).fiberι U1.point w'
          simp [w'', b, Scheme.Hom.fiberι_fiberHomeo_symm]
        refine ⟨w'', ?_⟩
        change (elementaryFiberIso f U1).hom (pB w'') = w
        rw [hp, hw']
    let e : fB.fiber U1.point ≅ T.toScheme :=
      IsOpenImmersion.isoOfRangeEq r T.ι (by simpa [Scheme.Opens.range_ι] using hrange)
    have hcomm : e.hom ≫ (T.ι ≫ f.fiberToSpecResidueField s) =
        fB.fiberToSpecResidueField U1.point ≫ Spec.map U1.residueFieldMap := by
      have he : e.hom ≫ T.ι = r := IsOpenImmersion.isoOfRangeEq_hom_fac r T.ι _
      rw [← Category.assoc, he]
      change (pB ≫ (elementaryFiberIso f U1).hom) ≫ f.fiberToSpecResidueField s = _
      rw [Category.assoc, elementaryFiberIso_hom_fiberToSpecResidueField, ← Category.assoc,
        fiberMapOfSourceHom_fiberToSpecResidueField]
    let : IsIso (Spec.map U1.residueFieldMap) := inferInstance
    exact MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso ⟨hcomm⟩)
      ‹GeometricallyConnected (T.ι ≫ f.fiberToSpecResidueField s)›
  obtain ⟨O, hOcompact, hOfiber, hOconn⟩ :=
    h057I fB q1 σ1 hσ U1.point hfBfp hZ1 hredB hconnB1
  let kO : O.toScheme ⟶ Yf1 := O.ι ≫ B1.ι
  have hkO : IsOpenImmersion kO := inferInstance
  let V1 : Yf1.Opens := ⟨Set.range kO, hkO.isOpen_range⟩
  let p1 : Yf1 ⟶ U1.scheme := pullback.snd f U1.toBase
  let qO : O.toScheme ⟶ U1.scheme := O.ι ≫ fB
  let pV1 : V1.toScheme ⟶ U1.scheme := V1.ι ≫ p1
  have hrangeO : Set.range kO = B1.ι '' (O : Set B1.toScheme) := by
    ext w
    exact ⟨fun ⟨o, ho⟩ => ⟨O.ι o, o.2, ho⟩, fun ⟨b, hb, hbw⟩ => ⟨⟨b, hb⟩, hbw⟩⟩
  have hV1compact : IsCompact (V1 : Set Yf1) := by
    change IsCompact (Set.range kO)
    rw [hrangeO]
    exact hOcompact.image B1.ι.continuous
  let eO : O.toScheme ≅ V1.toScheme :=
    IsOpenImmersion.isoOfRangeEq kO V1.ι (by
      simpa [Scheme.Opens.range_ι] using (show Set.range kO = (V1 : Set Yf1) from rfl))
  have heO : eO.hom ≫ V1.ι = kO := IsOpenImmersion.isoOfRangeEq_hom_fac kO V1.ι _
  have hqOeq : eO.hom ≫ pV1 = qO := by
    change eO.hom ≫ V1.ι ≫ p1 = O.ι ≫ B1.ι ≫ pullback.snd f U1.toBase
    rw [← Category.assoc, heO]
    simp [kO, p1]
  have hzbO (wb : fB.fiber U1.point) : fB.fiberι U1.point wb ∈ O := by
    have hmem : wb ∈ (fB.fiberι U1.point) ⁻¹ᵁ O := by rw [hOfiber]; trivial
    exact hmem
  have hV1fiber : ∀ w : p1.fiber U1.point,
      (p1.fiberι U1.point w ∈ V1) ↔
        pullback.fst f U1.toBase (p1.fiberι U1.point w) ∈ W := by
    intro w
    constructor
    · rintro ⟨o', ho'⟩
      rw [← ho']
      exact (O.ι o').property
    · intro hwW
      let b : B1.toScheme := ⟨p1.fiberι U1.point w, hwW⟩
      have hbbase : fB b = U1.point := (p1.fiberHomeo U1.point w).property
      let wb : fB.fiber U1.point := (fB.fiberHomeo U1.point).symm ⟨b, hbbase⟩
      have hbO : b ∈ O := by
        simpa [wb, Scheme.Hom.fiberι_fiberHomeo_symm] using hzbO wb
      exact ⟨⟨b, hbO⟩, rfl⟩
  let : UniversallyOpen qO := inferInstance
  let img : U1.scheme.Opens :=
    ⟨Set.range qO, by
      convert qO.isOpenMap (Set.univ : Set O.toScheme) isOpen_univ using 1
      ext w
      simp⟩
  have hfbNon : Nonempty (fB.fiber U1.point) := by
    obtain ⟨wq⟩ : Nonempty ((σ1 ≫ fB).fiber U1.point) := by rw [hσ]; exact hZ1
    exact ⟨fiberMapOfSourceHom σ1 fB U1.point wq⟩
  obtain ⟨wb⟩ := hfbNon
  have hImgpoint : U1.point ∈ img := by
    refine ⟨⟨fB.fiberι U1.point wb, hzbO wb⟩, ?_⟩
    change fB (fB.fiberι U1.point wb) = U1.point
    exact (fB.fiberHomeo U1.point wb).property
  obtain ⟨A2, hA2aff, hA2point, hA2subimg⟩ :=
    exists_isAffineOpen_mem_and_subset (U := img) hImgpoint
  have hA2res : ∀ p : A2.toScheme, IsIso (A2.ι.residueFieldMap p) := fun p => inferInstance
  let qOA := pullback.snd qO A2.ι
  have hqOAfiber : ∀ a : A2.toScheme, GeometricallyConnected (qOA.fiberToSpecResidueField a) := by
    intro a
    have hnon : Nonempty (qO.fiber (A2.ι a)) := by
      obtain ⟨o', ho'⟩ := hA2subimg a.2
      exact ⟨(qO.fiberHomeo (A2.ι a)).symm ⟨o', ho'⟩⟩
    let : IsIso (Spec.map (A2.ι.residueFieldMap a)) := inferInstance
    let : IsIso (baseChangeFiberMap qO A2.ι a) := isIso_baseChangeFiberMap qO A2.ι a
    exact MorphismProperty.of_isPullback
      (IsPullback.of_horiz_isIso ⟨baseChangeFiberMap_fiberToSpecResidueField qO A2.ι a⟩)
      (hOconn (A2.ι a) hnon)
  have hqOA : GeometricallyConnected qOA := by
    rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
    exact hqOAfiber
  let pVA := pullback.snd pV1 A2.ι
  let eOA : pullback qO A2.ι ⟶ pullback pV1 A2.ι :=
    pullback.map qO A2.ι pV1 A2.ι eO.hom (𝟙 A2.toScheme) (𝟙 U1.scheme)
      (by rw [hqOeq]; simp) (by simp)
  let : IsIso eO.hom := eO.isIso_hom
  let : IsIso eOA := by infer_instance
  let : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hqVA : GeometricallyConnected pVA := by
    have heval : eOA ≫ pVA = qOA := by
      change eOA ≫ pullback.snd pV1 A2.ι = pullback.snd qO A2.ι
      rw [pullback.lift_snd]
      simp
    refine (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyConnected) eOA pVA).mp ?_
    rw [heval]
    exact hqOA
  let U2 : EtaleNeighborhood S s :=
    { scheme := A2.toScheme
      point := ⟨U1.point, hA2point⟩
      toBase := A2.ι ≫ U1.toBase
      map_point := U1.map_point }
  have hU2 : U2.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact isIso_residueFieldMap_comp A2.ι U1.toBase ⟨U1.point, hA2point⟩ (hA2res _)
      ((U1.isElementary_iff).mp hU1)
  have hU2aff : IsAffine U2.scheme := hA2aff
  let Yf2 := pullback f U2.toBase
  let hP1 : IsPullback (pullback.fst p1 A2.ι) (pullback.snd p1 A2.ι) p1 A2.ι :=
    IsPullback.of_hasPullback p1 A2.ι
  let hOuter : IsPullback (pullback.fst p1 A2.ι ≫ pullback.fst f U1.toBase)
      (pullback.snd p1 A2.ι) f (A2.ι ≫ U1.toBase) :=
    hP1.paste_horiz (IsPullback.of_hasPullback f U1.toBase)
  let e12 : pullback p1 A2.ι ≅ Yf2 := hOuter.isoPullback
  let m12 : Yf2 ⟶ Yf1 := e12.inv ≫ pullback.fst p1 A2.ι
  let rA : Yf2 ⟶ A2.toScheme := e12.inv ≫ pullback.snd p1 A2.ι
  have hOuter2 : IsPullback m12 rA p1 A2.ι := by
    apply hP1.of_iso' e12.symm (Iso.refl Yf1) (Iso.refl A2.toScheme) (Iso.refl U1.scheme)
    · simp [m12, e12]
    · simp [rA, e12]
    · simp
    · rfl
  let hPVA : IsPullback (pullback.fst pV1 A2.ι) (pullback.snd pV1 A2.ι) pV1 A2.ι :=
    IsPullback.of_hasPullback pV1 A2.ι
  let hP3 : IsPullback (pullback.fst V1.ι m12) (pullback.snd V1.ι m12) V1.ι m12 :=
    IsPullback.of_hasPullback V1.ι m12
  let jV : pullback V1.ι m12 ⟶ Yf2 := pullback.snd V1.ι m12
  let hP3overA := hP3.paste_vert hOuter2
  let eP3VA : pullback V1.ι m12 ≅ pullback pV1 A2.ι :=
    hP3overA.isoPullback.trans hPVA.isoPullback.symm
  have heP3VA : eP3VA.hom ≫ pVA = jV ≫ rA := by
    calc
      eP3VA.hom ≫ pVA =
          hP3overA.isoPullback.hom ≫ (hPVA.isoPullback.inv ≫ pullback.snd pV1 A2.ι) := by
            simp [eP3VA, pVA]
      _ = hP3overA.isoPullback.hom ≫ pullback.snd (V1.ι ≫ p1) A2.ι := by
            rw [hPVA.isoPullback_inv_snd]
      _ = jV ≫ rA := hP3overA.isoPullback_hom_snd
  have hP3conn : GeometricallyConnected (jV ≫ rA) := by
    rw [← heP3VA]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyConnected) eP3VA.hom pVA).mpr hqVA
  let V2 : Yf2.Opens := m12 ⁻¹ᵁ V1
  have hV2range : Set.range jV = (V2 : Set Yf2) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_pullbackSnd]
    simp [V2]
  have hV2compact : IsCompact (V2 : Set Yf2) := by
    have hP3compact : IsCompact (Set.univ : Set ↥(pullback V1.ι m12)) := by
      let : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hOcompact
      let : IsAffine U1.scheme := hU1aff
      let : IsAffine A2.toScheme := hA2aff
      let : CompactSpace ↥(pullback qO A2.ι) := compactSpace_pullback_of_compactSpace qO A2.ι
      let : CompactSpace ↥(pullback pV1 A2.ι) := eOA.homeomorph.compactSpace
      let : CompactSpace ↥(pullback V1.ι m12) := eP3VA.inv.homeomorph.compactSpace
      exact isCompact_univ
    rw [← hV2range]
    simpa [Set.image_univ] using hP3compact.image jV.continuous
  let : CompactSpace V2.toScheme := isCompact_iff_compactSpace.mp hV2compact
  let : QuasiSeparatedSpace Yf2 :=
    AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated (pullback.snd f U2.toBase)
  have hV2qc : QuasiCompact V2.ι := AlgebraicGeometry.quasiCompact_of_compactSpace V2.ι
  let p2 : Yf2 ⟶ U2.scheme := pullback.snd f U2.toBase
  have hrA : rA = p2 := hOuter.isoPullback_inv_snd
  have hm12fst : m12 ≫ pullback.fst f U1.toBase = pullback.fst f U2.toBase :=
    hOuter.isoPullback_inv_fst
  let eV : pullback V1.ι m12 ≅ V2.toScheme :=
    IsOpenImmersion.isoOfRangeEq jV V2.ι (by simpa [Scheme.Opens.range_ι] using hV2range)
  have heV : eV.hom ≫ V2.ι = jV := IsOpenImmersion.isoOfRangeEq_hom_fac jV V2.ι _
  have hV2conn : GeometricallyConnected (V2.ι ≫ p2) := by
    refine (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyConnected) eV.hom (V2.ι ≫ p2)).mp ?_
    rw [← Category.assoc, heV, ← hrA]
    exact hP3conn
  refine ⟨U2, hU2, hU2aff, V2, hV2qc, hV2conn, ?_⟩
  let : IsIso U2.residueFieldMap := hU2
  intro w2
  let y2 : Yf2 := p2.fiberι U2.point w2
  have hy2 : p2 y2 = U2.point := (p2.fiberHomeo U2.point w2).property
  have hp1m : p1 (m12 y2) = U1.point := by
    calc
      p1 (m12 y2) = A2.ι (rA y2) := by
        simpa [Scheme.Hom.comp_apply] using
          congrArg (fun k : Yf2 ⟶ U1.scheme => k y2) hOuter2.w
      _ = A2.ι (p2 y2) := by rw [hrA]
      _ = U1.point := by rw [hy2]; rfl
  let w1 : p1.fiber U1.point := (p1.fiberHomeo U1.point).symm ⟨m12 y2, hp1m⟩
  have hfiber1 : p1.fiberι U1.point w1 = m12 y2 := by
    simp [w1, Scheme.Hom.fiberι_fiberHomeo_symm]
  have hfst : pullback.fst f U1.toBase (m12 y2) = pullback.fst f U2.toBase y2 := by
    simpa [Scheme.Hom.comp_apply] using congrArg (fun k : Yf2 ⟶ X => k y2) hm12fst
  have hOrig : f.fiberι s ((elementaryFiberIso f U2).hom w2) = pullback.fst f U2.toBase y2 := by
    simpa [y2, Scheme.Hom.comp_apply] using
      congrArg (fun k : p2.fiber U2.point ⟶ X => k w2) (elementaryFiberIso_hom_fiberι f U2)
  have hImage : pullback.fst f U2.toBase y2 ∈ f.fiberι s '' (T : Set (f.fiber s)) ↔
      (elementaryFiberIso f U2).hom w2 ∈ T := by
    refine ⟨fun ⟨w, hwT, hw⟩ => ?_, fun hw => ⟨_, hw, hOrig⟩⟩
    have hw' : w = (elementaryFiberIso f U2).hom w2 :=
      (f.fiberι s).isEmbedding.injective (hw.trans hOrig.symm)
    rw [← hw']
    exact hwT
  have hWiff : (elementaryFiberIso f U2).hom w2 ∈ T ↔ pullback.fst f U2.toBase y2 ∈ W := by
    rw [← hOrig, hWT]
  have hViff : y2 ∈ V2 ↔ pullback.fst f U2.toBase y2 ∈ W := by
    calc
      y2 ∈ V2 ↔ m12 y2 ∈ V1 := Iff.rfl
      _ ↔ p1.fiberι U1.point w1 ∈ V1 := by rw [hfiber1]
      _ ↔ pullback.fst f U1.toBase (p1.fiberι U1.point w1) ∈ W := hV1fiber w1
      _ ↔ pullback.fst f U2.toBase y2 ∈ W := by rw [hfiber1, hfst]
  change y2 ∈ V2 ↔ _
  exact hViff.trans (hWiff.symm.trans hImage.symm)

/-- **Stacks Project, Tag 055W** follows from Tag 0570 and Tag 057I. This also records that the
conditional Tag 055W proved here has exactly the binders of
`AlgebraicGeometry.Statement055W`. -/
theorem statement055W_of_statement0570_statement057I
    (h0570 : Statement0570.{u}) (h057I : Statement057I.{u}) : Statement055W.{u} :=
  fun f s T hfp ↦
    exists_elementaryEtaleNeighborhood_open_geometricallyConnected h0570 h057I f s T hfp

/-- **Stacks Project, Tag 055W** follows from Tag 0570 together with Tags 055P and 055R, which
are the two inputs of Tag 057I. -/
theorem statement055W_of_statement0570_statement055P_statement055R
    (h0570 : Statement0570.{u}) (h055P : Statement055P.{u}) (h055R : Statement055R.{u}) :
    Statement055W.{u} :=
  statement055W_of_statement0570_statement057I h0570
    (ConnectedComponentSection.statement057I h055P h055R)

end AlgebraicGeometry

end
