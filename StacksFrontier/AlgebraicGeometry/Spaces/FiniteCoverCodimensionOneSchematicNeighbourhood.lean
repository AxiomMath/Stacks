module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePreimageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealZerothSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFamilySchematicNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteNearCodimensionOnePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingStratumBlowupFlattening

/-!
# A finite cover by a scheme makes a point of codimension at most one schematic

This file assembles Steps 2 to 5 of the proof of Stacks 0ADD sketched in Stacks 0ADE, for a
given finite surjective morphism `U ⟶ X` from a scheme: the Fitting-stratum blowups of Step 2
(`AlgebraicGeometry.Space.exists_blowup_fittingStratum`) are made finite near `x` by Stacks 0AD2
and restricted over a common neighbourhood `N` of `x`, where their strict transforms are schemes;
the resulting finite family is fed to Steps 3 to 5
(`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_finite_family`).

## Main results

* `exists_isOpen_subset_closure_singleton_of_mem_genericPoints`: in a Noetherian topological
  space a generic point of an irreducible component has an open neighbourhood consisting of its
  specializations.
* `AlgebraicGeometry.Space.localRingDimension_ne_zero_of_mem_of_dense_compl`: a closed set of
  points of a locally Noetherian algebraic space with dense complement contains no point of
  codimension zero.
* `AlgebraicGeometry.Space.exists_yoneda_isFiniteLocallyFree_of_restrict`: a blown-up stratum
  restricted over an open on which it is finite has a scheme as strict transform.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_isFinite_isSurjective_cover`:
  **Steps 2 to 5 of Stacks 0ADE** for a given finite surjective cover by a scheme.

## References

* [Stacks Project, Tag 0ADE](https://stacks.math.columbia.edu/tag/0ADE)
* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **A generic point of an irreducible component of a Noetherian space has an open
neighbourhood inside its closure**: the complement of the union of the finitely many other
irreducible components. -/
theorem exists_isOpen_subset_closure_singleton_of_mem_genericPoints {α : Type*}
    [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] {v : α} (hv : v ∈ genericPoints α) :
    ∃ O : Set α, IsOpen O ∧ v ∈ O ∧ O ⊆ closure {v} := by
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  set C := closure ({v} : Set α) with hC
  set R := irreducibleComponents α \ {C} with hR
  have hRfin : R.Finite := hfin.sdiff
  refine ⟨(⋃₀ R)ᶜ, (hRfin.isClosed_sUnion fun D hD => isClosed_of_mem_irreducibleComponents D
    hD.1).isOpen_compl, ?_, ?_⟩
  · rintro ⟨D, ⟨hD, hDC⟩, hvD⟩
    apply hDC
    have hCD : C ⊆ D := closure_minimal (Set.singleton_subset_iff.2 hvD)
      (isClosed_of_mem_irreducibleComponents D hD)
    exact (hv.2 hD.1 hCD).antisymm hCD |>.symm ▸ rfl
  · intro y hy
    obtain ⟨D, hD, hyD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({y} : Set α)) isIrreducible_singleton.closure
    by_cases hDC : D = C
    · exact hDC ▸ hyD (subset_closure (Set.mem_singleton y))
    · exact absurd ⟨D, ⟨hD, hDC⟩, hyD (subset_closure (Set.mem_singleton y))⟩ hy

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed set of points with dense complement contains no point of codimension zero**, on a
locally Noetherian algebraic space.  On an affine étale chart through such a point the point
over it is a generic point of an irreducible component (Stacks 0BAQ), which has an open
neighbourhood of specializations; its image is an open neighbourhood of the point inside the
closed set, which the dense complement must meet.

Applied to the exceptional divisor of a blowup, whose complement is dense (Stacks 083S), this is
what keeps the points of codimension zero out of the locus `Z` of Step 4 of Stacks 0ADE. -/
theorem localRingDimension_ne_zero_of_mem_of_dense_compl {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (E : Set (points B S hS X)) (hE : IsClosed E) (hdense : Dense Eᶜ)
    (a : points B S hS X) (ha : a ∈ E) : localRingDimension B S hS a ≠ 0 := by
  intro h0
  obtain ⟨V, φ, hVaff, hφet, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X hX a
  have := hVaff
  have hφet' := (isEtale_iff_presheaf_of_yoneda B S hS φ).mpr hφet
  have hVnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).1
      (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (isAlgebraicSpace_yoneda B S hS V) hX φ
        (isLocallyOfFiniteType_of_isEtale B S hS hX hφet') hnoeth)
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V) := {}
  have hgen : pointsToScheme B S hS V w ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj V) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX a).1 h0 V φ _ hφet'
      (hw ▸ chartPoint_pointsToScheme B S hS V φ w)
  obtain ⟨Ov, hOv, hwOv, hOvsub⟩ := exists_isOpen_subset_closure_singleton_of_mem_genericPoints hgen
  -- the image of `Ov` in `|X|`
  set W := pointsMap B S hS _ φ '' (pointsToScheme B S hS V ⁻¹' Ov) with hWdef
  have hWopen : IsOpen W :=
    isOpenMap_pointsMap_of_isEtale B S hS φ (isAlgebraicSpace_yoneda B S hS V) hX hφet' _
      (hOv.preimage (schemePointsHomeomorph B S hS V).continuous)
  have hWE : W ⊆ E := by
    rintro _ ⟨o, ho, rfl⟩
    have hspec : w ⤳ o := by
      have h1 : pointsToScheme B S hS V w ⤳ pointsToScheme B S hS V o :=
        specializes_iff_mem_closure.2 (hOvsub ho)
      have h2 := h1.map (schemePointsHomeomorph B S hS V).symm.continuous
      rwa [← schemePointsHomeomorph_apply, ← schemePointsHomeomorph_apply,
        Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at h2
    have h3 := hspec.map (continuous_pointsMap B S hS φ)
    rw [hw] at h3
    exact h3.mem_closed hE ha
  obtain ⟨y, hyW, hyc⟩ := hdense.inter_open_nonempty W hWopen ⟨a, w, hwOv, hw⟩
  exact hyc (hWE hyW)

/-- **A blown-up stratum restricted over an open on which it is finite.**  Let `g : h_U ⟶ X` be
finite, `p : X' ⟶ X` a morphism, `q : Y' ⟶ X'` surjective and finite locally free, and
`σ : Y' ⟶ h_U` with `σ ≫ g = q ≫ p`.  Over an open subspace `N ⊆ X` above which `p` is finite,
the restriction `Y' ×_X N ⟶ X' ×_X N` of `q` is a surjective finite locally free morphism out of
a *scheme* of the site: `Y' ×_X N` is finite over `h_U ×_X N`, an open subscheme of `U`.

This is the point where the source's "then `Y'` is a scheme" is proved: the strict transform
`Y' ⊆ X' ×_X Y` is finite over the scheme `Y` once `X' ⟶ X` is finite. -/
theorem exists_yoneda_isFiniteLocallyFree_of_restrict {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X)
    (hg : IsFinite B S hS g) {X' Y' : AlgebraicSpaces B S hS} (p : X'.1 ⟶ X) (q : Y' ⟶ X')
    (hq : IsFiniteLocallyFree B S hS q) (hqs : IsSurjective B S hS q.hom) (σ : Y'.1 ⟶ yoneda.obj U)
    (hσ : σ ≫ g = q.hom ≫ p) (N : Subfunctor X) (hN : IsOpenSubspace B S hS N)
    (hpN : IsFinite B S hS (N.fromPreimage p)) :
    ∃ (Y'' : BigFppfOver B S hS) (h : yoneda.obj Y'' ⟶ (N.preimage p).toFunctor),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf h ∧
      (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf h := by
  classical
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  set Xs := N.preimage p with hXs
  set Ys := Xs.preimage q.hom with hYs
  have hXsopen : IsOpenSubspace B S hS Xs := isOpenSubspace_preimage B S hS p N hX X'.2 hN
  have hYsopen : IsOpenSubspace B S hS Ys :=
    isOpenSubspace_preimage B S hS q.hom Xs X'.2 Y'.2 hXsopen
  set q'' := Xs.fromPreimage q.hom with hq''
  have sqq : IsPullback q'' Ys.ι Xs.ι q.hom := Subfunctor.isPullback_preimage q.hom Xs
  have hqpre := (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS q).2 hq
  have hq''flf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q'' :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqq.flip hqpre
  have hq''surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q'' := by
    refine presheafSurjective_of_isSurjective B S hS q'' hq''flf.rep fun z => ?_
    obtain ⟨y, hy⟩ := hqs (pointsMap B S hS _ Xs.ι z)
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS sqq z y hy.symm
    exact ⟨w, hw⟩
  -- `Ys` is a scheme: it is finite over the open subscheme `N.preimage g` of `U`
  have hle : Subfunctor.range (Ys.ι ≫ σ) ≤ N.preimage g := by
    rintro T _ ⟨s, rfl⟩
    have h1 : g.app T (σ.app T s.1) = p.app T (q.hom.app T s.1) :=
      congrFun (congrArg (fun φ => φ.app T) hσ) s.1
    change g.app T (σ.app T s.1) ∈ N.obj T
    rw [h1]
    exact s.2
  set τ := Subfunctor.lift (Ys.ι ≫ σ) hle with hτ
  have hgN : IsFinite B S hS (N.fromPreimage g) :=
    isFinite_of_isPullback B S hS (Subfunctor.isPullback_preimage g N).flip hg
  have hNg := isOpenSubspace_preimage B S hS g N hX hUalg hN
  have hgNalg : IsAlgebraicSpace B S hS (N.preimage g).toFunctor := hNg.1
  have hcomp : τ ≫ N.fromPreimage g = q'' ≫ N.fromPreimage p := by
    apply (cancel_mono N.ι).1
    simp only [Category.assoc, Subfunctor.fromPreimage_ι]
    rw [← Category.assoc, Subfunctor.lift_ι, Category.assoc, hσ, ← Category.assoc,
      ← Subfunctor.fromPreimage_ι, Category.assoc]
  have hq''fin : IsFinite B S hS q'' := (isFinite_iff_representable B S hS q'' hYsopen.1
      hXsopen.1).2 ⟨hq''flf.rep, MorphismProperty.relative_monotone (F := yoneda)
        (fun A C k hk => by
          have : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map k) := hk
          exact Stacks.Morphisms.IsFiniteLocallyFree.isFinite _) _ hq''flf⟩
  have hτfin : IsFinite B S hS τ := by
    refine isFinite_of_comp_of_isSeparated B S hS τ (N.fromPreimage g) ?_
      (isSeparated_of_isFinite B S hS _ hgNalg hN.1 hgN)
    rw [hcomp]
    exact isFinite_comp B S hS hq''fin hpN
  have hYsrep : Ys.toFunctor.IsRepresentable :=
    isRepresentable_of_relativelyRepresentable_of_target B S hS τ
      ((isFinite_iff_representable B S hS τ hYsopen.1 hgNalg).1 hτfin).1
      (isRepresentable_of_isOpenSubspace_yoneda B S hS U _ hNg)
  refine ⟨Ys.toFunctor.reprX, Ys.toFunctor.reprW.hom ≫ q'', ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.precomp _ _ _ hq''surj
  · exact MorphismProperty.RespectsIso.precomp _ _ _ hq''flf

/-- **Stacks 0ADD, given a finite surjective cover by a scheme, along the route of Stacks 0ADE.**
Let `X` be a separated, locally Noetherian algebraic space over `S`, let `g : h_U ⟶ X` be a
finite surjective morphism from a scheme of the site, and let `x ∈ |X|` be a point whose local
ring has dimension at most one.  Then `x` lies in an open subspace of `X` which is an affine
scheme.

* **Step 2.**  Let `Z_0 ⊇ Z_1 ⊇ ⋯` be the closed subspaces cut out by the Fitting ideals of
  `g_*𝒪_U` (Stacks 0CZ9); `|Z_0|` is all of `|X|` (the support of `g_*𝒪_U`) and the `|Z_r|`
  have empty intersection, so `x` lies in the strata `Z_k ∖ Z_{k+1}` for exactly one `k < m`,
  where `m` is least with `x ∉ |Z_m|`.  For each `k < m`, blowing up `Z_k` in its Fitting
  centre gives a proper `X'_k ⟶ X` which is an isomorphism over the stratum from a dense open,
  with a surjective finite locally free strict transform `Y'_k ⟶ X'_k`
  (`AlgebraicGeometry.Space.exists_blowup_fittingStratum`).  By Stacks 0AD2 each `X'_k ⟶ X` is
  finite over a neighbourhood of `x`; over the intersection `N` of those neighbourhoods with
  `|X| ∖ |Z_m|` the strict transforms are schemes
  (`AlgebraicGeometry.Space.exists_yoneda_isFiniteLocallyFree_of_restrict`).
* The family `X'_k ×_X N ⟶ N` covers `|N|` and is injective off the closed set `Z` of images of
  the exceptional divisors, which contains no point of codimension zero
  (`AlgebraicGeometry.Space.localRingDimension_ne_zero_of_mem_of_dense_compl`).
* **Steps 3–5** are
  `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_finite_family`.
-/
theorem exists_isOpenSubspace_isRepresentable_of_isFinite_isSurjective_cover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X) (hgfin : IsFinite B S hS g)
    (hgsurj : IsSurjective B S hS g) (x : points B S hS X)
    (hdim : localRingDimension B S hS x ≤ 1) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ IsAffineSpace B S hS G.toFunctor ∧
      x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let Xb : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ub : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hUalg⟩
  let gb : Ub ⟶ Xb := ObjectProperty.homMk g
  -- the Fitting closed subspaces of `g_*𝒪_U`
  set F := pushforwardStructureModule B S hS gb with hFdef
  have hUnoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hUalg hX g
    (isLocallyOfFiniteType_of_isFinite B S hS hUalg hX hgfin) hnoeth
  have hFcoh : IsCoherent B S hS X hX F := by
    have : Fact (HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) := ⟨hUnoeth⟩
    exact isCoherent_modulePushforward_of_isFinite' B S hS gb hgfin hnoeth _
      (isCoherent_structureSheaf B S hS (yoneda.obj U) hUalg)
  have hFqc : F.IsQuasicoherentOnSite := hFcoh.toIsQuasicoherentOnSite
  have := SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite F hFcoh.toIsCoherentOnSite
  have hFft : SheafOfModules.IsFiniteTypeOnSite F := inferInstance
  have hFfin := module_finite_sections_of_isFiniteTypeOnSite F hFqc hFft
  obtain ⟨Zc, hZc, hanti, -⟩ :=
    exists_fittingClosedSubspaces_of_isFiniteTypeOnSite B S hS Xb F hFqc hFft
  have hinter := iInter_range_pointsMap_ι_fittingClosedSubspace_eq_empty B S hS Xb F Zc hZc hFfin
  have hZ0 : ∀ y : points B S hS X, y ∈ Set.range (pointsMap B S hS _ (Zc 0).1.ι) := by
    intro y
    have hsupp := supportOfSheaf_modulePushforward_structureSheaf_eq_univ B S hS gb hgsurj
    have hsub := supportOfSheaf_subset_idealZeroLocus_fittingIdeal_zero B S hS Xb F
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX F hFqc) hFfin
    rw [range_pointsMap_ι_eq_idealZeroLocus B S hS Xb (Zc 0), hZc 0]
    exact hsub (hsupp ▸ Set.mem_univ y)
  have hmono : ∀ {r s : ℕ}, r ≤ s → Set.range (pointsMap B S hS _ (Zc s).1.ι) ⊆
      Set.range (pointsMap B S hS _ (Zc r).1.ι) := by
    intro r s hrs
    rintro _ ⟨z, rfl⟩
    refine ⟨pointsMap B S hS _ (Subfunctor.homOfLe (hanti hrs)) z, ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  have hex : ∀ y : points B S hS X, ∃ r, y ∉ Set.range (pointsMap B S hS _ (Zc r).1.ι) := by
    intro y
    by_contra h
    simp only [not_exists, not_not] at h
    have : y ∈ ⋂ r, Set.range (pointsMap B S hS _ (Zc r).1.ι) := Set.mem_iInter.2 h
    rw [hinter] at this
    exact this
  set m := Nat.find (hex x) with hm
  -- the blown-up strata `k < m`
  choose X' Y' p q σ O hp hO hOdense hland hOiff hmonoO hlftO hsurjO hq hqs hσ using
    fun k : Fin m => exists_blowup_fittingStratum B S hS hnoeth gb hgfin hgsurj Zc hZc k
  have hσ' : ∀ k, (σ k).hom ≫ g = (q k).hom ≫ (p k).hom := fun k =>
    congrArg (fun ψ : Y' k ⟶ Xb => ψ.hom) (hσ k)
  -- Stacks 0AD2: each `X'_k ⟶ X` is finite over a neighbourhood of `x`
  choose V hV hxV hVfin using fun k : Fin m =>
    exists_isOpenSubspace_isFinite_pullback_snd_of_localRingDimension_le_one B S hS (X' k).2 hX
      (p k).hom (hp k) hnoeth x hdim (Or.inr (Or.inr (Or.inr ((hOdense k).mono (by
        rintro _ ⟨o, rfl⟩
        exact ⟨O k, hO k, o, rfl, isLocallyQuasiFinite_of_mono B S hS (hO k).1 hX _ (hmonoO k)
          (hlftO k)⟩)))))
  -- the common neighbourhood `N` of `x`
  set Nset := (⋂ k, Set.range (pointsMap B S hS (V k).toFunctor (V k).ι)) ∩
    (Set.range (pointsMap B S hS _ (Zc m).1.ι))ᶜ with hNset
  have hNopen : IsOpen Nset :=
    (isOpen_iInter_of_finite fun k =>
      isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hV k).2).inter
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX _ (Zc m).2.2).isOpen_compl
  obtain ⟨N, hN, hNrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX Nset hNopen
  have hxN : x ∈ Set.range (pointsMap B S hS N.toFunctor N.ι) := by
    rw [hNrange]
    exact ⟨Set.mem_iInter.2 hxV, Nat.find_spec (hex x)⟩
  have hsqN : ∀ k, IsPullback (N.fromPreimage (p k).hom) (N.preimage (p k).hom).ι N.ι
      (p k).hom := fun k => Subfunctor.isPullback_preimage _ N
  -- finiteness over `N`
  have hpN : ∀ k, IsFinite B S hS (N.fromPreimage (p k).hom) := by
    intro k
    have hle : N ≤ V k := le_of_range_pointsMap_ι_subset B S hS (hV k) (by
      rw [hNrange]
      exact fun y hy => Set.mem_iInter.1 hy.1 k)
    have hk : IsPullback (pullback.lift (N.preimage (p k).hom).ι
        (N.fromPreimage (p k).hom ≫ Subfunctor.homOfLe hle)
        (by rw [Category.assoc, Subfunctor.homOfLe_ι, (hsqN k).w]))
        (N.fromPreimage (p k).hom) (pullback.snd (p k).hom (V k).ι) (Subfunctor.homOfLe hle) :=
      IsPullback.of_right (by rw [pullback.lift_fst, Subfunctor.homOfLe_ι]; exact (hsqN k).flip)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback (p k).hom (V k).ι)
    exact isFinite_of_isPullback B S hS hk (hVfin k)
  -- the restricted strict transforms are schemes
  choose Y'' h hhs hhflf using fun k =>
    exists_yoneda_isFiniteLocallyFree_of_restrict B S hS hX U g hgfin (p k).hom (q k) (hq k)
      (hqs k) (σ k).hom (hσ' k) N hN (hpN k)
  -- `N` is separated and locally Noetherian, and `x` has dimension at most one on it
  have hsepN : IsAbsolutelySeparated B S hS B.contains_terminal N.toFunctor :=
    isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep
      (isSeparated_of_mono N.ι inferInstance)
  have hnoethN : HasEtaleLocalProperty B S hS N.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hN.1 hX N.ι
      (isLocallyOfFiniteType_of_isEtale B S hS hX (isEtale_of_isOpenImmersion B S hS hN.2)) hnoeth
  obtain ⟨xN, hxN'⟩ := hxN
  have hdimN : localRingDimension B S hS xN ≤ 1 := by
    rw [← localRingDimension_pointsMap_of_etale B S hS hN.1 hX N.ι
      (isEtale_of_isOpenImmersion B S hS hN.2) xN, hxN']
    exact hdim
  have hNp := fun k => isOpenSubspace_preimage B S hS (p k).hom N hX (X' k).2 hN
  have hX'' : ∀ k, IsAlgebraicSpace B S hS (N.preimage (p k).hom).toFunctor := fun k => (hNp k).1
  -- the locus `Z` of non-injectivity: the images of the exceptional divisors
  set E := fun k => {a : points B S hS (N.preimage (p k).hom).toFunctor |
    pointsMap B S hS _ (N.preimage (p k).hom).ι a ∉
      Set.range (pointsMap B S hS (O k).toFunctor (O k).ι)} with hEdef
  have hEclosed : ∀ k, IsClosed (E k) := fun k =>
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hO k).2).isClosed_compl.preimage
      (continuous_pointsMap B S hS _)
  set Z := ⋃ k, pointsMap B S hS _ (N.fromPreimage (p k).hom) '' E k with hZdef
  have hZ : IsClosed Z := isClosed_iUnion_of_finite fun k =>
    isClosed_image_pointsMap_of_isFinite B S hS (hX'' k) hN.1 _ (hpN k) (hEclosed k)
  -- `Z` contains no point of codimension zero: the exceptional divisors have dense complement
  have hZ0' : ∀ z ∈ Z, localRingDimension B S hS z ≠ 0 := by
    intro z hz hz0
    obtain ⟨k, a, ha, rfl⟩ := Set.mem_iUnion.1 hz |>.imp fun k h => h
    have hlqf := isLocallyQuasiFinite_of_isFinite B S hS (hX'' k) hN.1 (hpN k)
    have hle := localRingDimension_le_of_isLocallyQuasiFinite B S hS (hX'' k) hN.1 _ hlqf a
    rw [hz0] at hle
    have ha0 : localRingDimension B S hS a = 0 := le_antisymm hle (by simp)
    have hnoeth'' : HasEtaleLocalProperty B S hS (N.preimage (p k).hom).toFunctor
        (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
      isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (hX'' k) hN.1 _
        (isLocallyOfFiniteType_of_isFinite B S hS (hX'' k) hN.1 (hpN k)) hnoethN
    have hdense : Dense (E k)ᶜ := by
      have : (E k)ᶜ = pointsMap B S hS _ (N.preimage (p k).hom).ι ⁻¹'
          Set.range (pointsMap B S hS (O k).toFunctor (O k).ι) := by
        ext b
        simp [hEdef]
      rw [this]
      exact (hOdense k).preimage (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ (hNp k).2)
    exact localRingDimension_ne_zero_of_mem_of_dense_compl B S hS (hX'' k) hnoeth'' (E k)
      (hEclosed k) hdense a ha ha0
  -- the family covers `|N|`
  have hcover : ∀ y : points B S hS N.toFunctor, ∃ k : Fin m,
      ∃ a : points B S hS (N.preimage (p k).hom).toFunctor,
        pointsMap B S hS _ (N.fromPreimage (p k).hom) a = y := by
    intro y
    set y₀ := pointsMap B S hS _ N.ι y with hy₀
    have hy₀N : y₀ ∈ Nset := hNrange ▸ ⟨y, rfl⟩
    have hsm : Nat.find (hex y₀) ≤ m := Nat.find_min' (hex y₀) hy₀N.2
    have hs0 : Nat.find (hex y₀) ≠ 0 := by
      intro h
      have := Nat.find_spec (hex y₀)
      rw [h] at this
      exact this (hZ0 y₀)
    obtain ⟨s', hs'⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hlt : s' < m := by omega
    have hin : y₀ ∈ Set.range (pointsMap B S hS _ (Zc s').1.ι) := by
      by_contra h
      exact Nat.find_min (hex y₀) (by omega : s' < Nat.find (hex y₀)) h
    have hout : y₀ ∉ Set.range (pointsMap B S hS _ (Zc (s' + 1)).1.ι) := by
      have := Nat.find_spec (hex y₀)
      rwa [hs'] at this
    obtain ⟨a, ha⟩ := hsurjO ⟨s', hlt⟩ y₀ hin hout
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS (hsqN ⟨s', hlt⟩) y a ha.symm
    exact ⟨⟨s', hlt⟩, w, hw⟩
  -- the family is injective off `Z`
  have hinj : ∀ y ∉ Z, ∀ (k k' : Fin m) (a : points B S hS (N.preimage (p k).hom).toFunctor)
      (a' : points B S hS (N.preimage (p k').hom).toFunctor),
      pointsMap B S hS _ (N.fromPreimage (p k).hom) a = y →
        pointsMap B S hS _ (N.fromPreimage (p k').hom) a' = y →
          (⟨k, a⟩ : Σ k, points B S hS (N.preimage (p k).hom).toFunctor) = ⟨k', a'⟩ := by
    intro y hyZ k k' a a' ha ha'
    have hO' : ∀ (j : Fin m) (b : points B S hS (N.preimage (p j).hom).toFunctor),
        pointsMap B S hS _ (N.fromPreimage (p j).hom) b = y →
          pointsMap B S hS _ (N.preimage (p j).hom).ι b ∈
            Set.range (pointsMap B S hS (O j).toFunctor (O j).ι) := by
      intro j b hb
      by_contra hbO
      exact hyZ (Set.mem_iUnion.2 ⟨j, b, hbO, hb⟩)
    have hpy : ∀ (j : Fin m) (b : points B S hS (N.preimage (p j).hom).toFunctor),
        pointsMap B S hS _ (N.fromPreimage (p j).hom) b = y →
          pointsMap B S hS _ (p j).hom (pointsMap B S hS _ (N.preimage (p j).hom).ι b) =
            pointsMap B S hS _ N.ι y := by
      intro j b hb
      rw [← pointsMap_comp_apply, ← (hsqN j).w, pointsMap_comp_apply, hb]
    have hstr : ∀ (j : Fin m) (b : points B S hS (N.preimage (p j).hom).toFunctor),
        pointsMap B S hS _ (N.fromPreimage (p j).hom) b = y →
          pointsMap B S hS _ N.ι y ∈ Set.range (pointsMap B S hS _ (Zc j).1.ι) ∧
            pointsMap B S hS _ N.ι y ∉ Set.range (pointsMap B S hS _ (Zc (j + 1)).1.ι) := by
      intro j b hb
      have h0 := hland j (pointsMap B S hS _ (N.preimage (p j).hom).ι b)
      rw [hpy j b hb] at h0
      refine ⟨h0, ?_⟩
      have := (hOiff j _).1 (hO' j b hb)
      rwa [hpy j b hb] at this
    have hkk : k = k' := by
      obtain ⟨h1, h2⟩ := hstr k a ha
      obtain ⟨h1', h2'⟩ := hstr k' a' ha'
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact h2 (hmono (by omega) h1')
      · exact h2' (hmono (by omega) h1)
    subst hkk
    obtain ⟨o, ho⟩ := hO' k a ha
    obtain ⟨o', ho'⟩ := hO' k a' ha'
    have := hmonoO k
    have hoo : o = o' := pointsMap_injective_of_mono B S hS ((O k).ι ≫ (p k).hom) (by
      rw [pointsMap_comp_apply B S hS (O k).ι (p k).hom o,
        pointsMap_comp_apply B S hS (O k).ι (p k).hom o', ho, ho', hpy k a ha, hpy k a' ha'])
    have haa : a = a' := pointsMap_injective_of_mono B S hS (N.preimage (p k).hom).ι (by
      rw [← ho, ← ho', hoo])
    rw [haa]
  -- Steps 3, 4 and 5
  obtain ⟨W, hW, hWaff, hxW⟩ := exists_isOpenSubspace_isRepresentable_of_finite_family B S hS
    hN.1 hsepN hnoethN xN hdimN (fun k => (N.preimage (p k).hom).toFunctor) hX''
    (fun k => N.fromPreimage (p k).hom) hpN Y'' h hhs hhflf Z hZ hZ0' hcover hinj
  obtain ⟨K, hK, hKaff, hKrange⟩ :=
    exists_isOpenSubspace_isAffineSpace_of_isOpenSubspace B S hS hN hW hWaff
  refine ⟨K, hK, hKaff, ?_⟩
  rw [hKrange, ← hxN']
  obtain ⟨w, hw⟩ := hxW
  exact ⟨w, by rw [pointsMap_comp_apply, hw]⟩

end AlgebraicGeometry.Space

end
