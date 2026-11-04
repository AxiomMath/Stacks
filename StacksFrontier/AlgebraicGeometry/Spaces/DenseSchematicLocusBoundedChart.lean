module

public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.FppfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedChartTopStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstantFibreDegreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative

/-!
# The schematic locus of a space with a bounded affine chart

Stacks 03JI says that a reasonable algebraic space has a dense open subspace which is a scheme.
This file proves that conclusion for a space presented by a *single* surjective étale chart by an
affine scheme whose fibres are universally bounded in the sense of Stacks 03JL.

## Main results

* `AlgebraicGeometry.Space.property_map_snd_of_isPullback`: the fibre of a base change agrees
  with the fibre of the original morphism above the composed test morphism.
* `AlgebraicGeometry.Space.exists_chart_openSubspaceOfPoints`: **the restriction of an étale
  chart to an open subspace.** For a surjective étale chart `φ : h_U ⟶ X` and an open set `W` of
  points of `X`, an open subscheme `V ⊆ U` and a surjective étale chart
  `ψ : h_V ⟶ X_W` of the open subspace cut out by `W`, with the Cartesian square relating the
  two.
* `AlgebraicGeometry.Space.exists_affineOpen_containing_finite_of_isOpenImmersion_isAffine`:
  Stacks 01ZY for an open subscheme of an affine scheme.
* `isRepresentable_of_presheafSurjective_presheafEtale_of_isFiniteLocallyFree_relation`, in the
  namespace `AlgebraicGeometry.Space`: an algebraic space over `S` with a surjective étale chart
  whose self base change is finite locally free, and whose finite sets of points lie in affine
  opens, is representable.
* `exists_denseRange_isRepresentable_isOpenSubspace_of_boundedAffineChart`, in the namespace
  `AlgebraicGeometry.Space`: the conclusion of Stacks 03JI for a space presented by one bounded
  affine chart.

## Implementation notes

The last result is not tagged: Stacks 03JI assumes the space reasonable (condition (2) of
Stacks 03JT), whereas this one assumes a single surjective étale chart by an affine scheme with
bounded fibres. `AlgebraicGeometry.Space.exists_boundedEtaleCover_of_isReasonableSpace` gives
only a jointly surjective family of such charts (condition (1) of Stacks 03JT).

`AlgebraicGeometry.Space.property_map_snd_of_isPullback` and
`AlgebraicGeometry.Space.property_map_snd_yoneda_map_comp_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.ConstantFibreDegreeChart` are different statements and
neither subsumes the other: the latter restricts the test morphism, the former the morphism being
base changed. Keep both until a common generalisation, with both edges variable, is written.

## References

* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre of a base change -/

/-- **The fibre of a base change.** Let `ψ : h_V ⟶ Z` be the base change of `φ : h_U ⟶ X` along
`κ : Z ⟶ X`. Then for a test morphism `a : h_T ⟶ Z` the scheme representing the fibre of `ψ`
above `a` and the one representing the fibre of `φ` above `a ≫ κ` are isomorphic over `T`, so any
property of morphisms of schemes which respects isomorphisms holds of one exactly when it holds
of the other. -/
theorem property_map_snd_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X} (hφ : yoneda.relativelyRepresentable φ)
    {ψ : yoneda.obj V ⟶ Z} (hψ : yoneda.relativelyRepresentable ψ)
    {κ : Z ⟶ X} {j : V ⟶ U} (hsq : IsPullback ψ (yoneda.map j) κ φ)
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Z) :
    P ((BigFppfOver.toScheme B S hS).map (hψ.snd a)) ↔
      P ((BigFppfOver.toScheme B S hS).map (hφ.snd (a ≫ κ))) := by
  set F := BigFppfOver.toScheme B S hS with hF
  have hpaste : IsPullback (hψ.fst a ≫ yoneda.map j) (yoneda.map (hψ.snd a)) φ (a ≫ κ) :=
    ((hψ.isPullback a).flip.paste_vert hsq).flip
  set e := yoneda.preimageIso
    (hpaste.isoIsPullback _ _ (hφ.isPullback (a ≫ κ))) with hedef
  have he : e.hom ≫ hφ.snd (a ≫ κ) = hψ.snd a := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hedef]
    simp only [Functor.preimageIso_hom, Functor.map_preimage]
    exact hpaste.isoIsPullback_hom_snd _ _ (hφ.isPullback (a ≫ κ))
  have hiso : IsIso (F.map e.hom) := (F.mapIso e).isIso_hom
  rw [← he, F.map_comp]
  exact P.cancel_left_of_respectsIso (F.map e.hom) _

/-! ### Finite sets of points of an open subscheme of an affine scheme -/

/-- **Stacks 01ZY for an open subscheme of an affine scheme.** If a scheme admits an open
immersion into an affine scheme then every finite set of its points lies in an affine open. -/
theorem exists_affineOpen_containing_finite_of_isOpenImmersion_isAffine {V U : Scheme.{u}}
    (i : V ⟶ U) [_root_.AlgebraicGeometry.IsOpenImmersion i] [IsAffine U]
    {E : Set V} (hE : E.Finite) : ∃ O : V.Opens, IsAffineOpen O ∧ E ⊆ O :=
  Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_affine i hE

/-! ### Restricting a chart to an open subspace -/

/-- **The restriction of an étale chart to an open subspace.** Let `φ : h_U ⟶ X` be a surjective
étale chart of a presheaf on the big fppf site of `S` and let `W` be an open set of points of `X`.
Then the open subspace of Stacks 03BZ cut out by `W` has a surjective étale chart by an open
subscheme `V` of `U`: the inverse image of `W`, which is an open subscheme because `W` is open for
the point topology of Stacks 03BX. -/
theorem exists_chart_openSubspaceOfPoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (W : Set (points B S hS X)) (hW : IsOpen W) :
    ∃ (V : BigFppfOver B S hS) (i : V ⟶ U)
      (ψ : yoneda.obj V ⟶ (openSubspaceOfPoints B S hS X W).toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
        IsPullback ψ (yoneda.map i) (openSubspaceOfPoints B S hS X W).ι φ ∧
        (MorphismProperty.inverseImage (@Surjective.{u})
          (BigFppfOver.toScheme B S hS)).presheaf ψ ∧
        (MorphismProperty.inverseImage (@Etale.{u})
          (BigFppfOver.toScheme B S hS)).presheaf ψ := by
  set Z := openSubspaceOfPoints B S hS X W with hZdef
  rw [isOpen_pointTopology_iff] at hW
  obtain ⟨V₀, hV₀, hpoints⟩ := hW U φ
  obtain ⟨V, i, hi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver U ⟨V₀, hV₀⟩
  have hmono : Mono i := inverseImage_isOpenImmersion_le_monomorphisms i hi
  have hmi : Mono (yoneda.map i) := inferInstance
  have hkey : Subfunctor.range (yoneda.map i) = Z.preimage φ :=
    range_yoneda_map_eq_preimage_openSubspaceOfPoints B S hS W φ i V₀ hirange hiuniv hpoints
  have hiso := Subfunctor.isIso_lift hkey.le hkey.ge
  have hsq := Subfunctor.isPullback_fromPreimage Z φ
  have hpb : IsPullback (Subfunctor.lift (yoneda.map i) hkey.le ≫ Z.fromPreimage φ)
      (yoneda.map i) Z.ι φ :=
    hsq.of_iso' (asIso (Subfunctor.lift (yoneda.map i) hkey.le)) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have hbc : ∀ P : MorphismProperty (BigFppfOver B S hS), P.presheaf φ →
      P.presheaf (Subfunctor.lift (yoneda.map i) hkey.le ≫ Z.fromPreimage φ) := fun P h =>
    (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback hpb.flip h
  exact ⟨V, i, _, hi, hpb, hbc _ hsurj, hbc _ hetale⟩

/-- The Yoneda transpose of the image of a section under a morphism of presheaves is the
transpose of the section followed by that morphism. -/
private theorem yonedaEquiv_symm_app {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    {T : BigFppfOver B S hS} (x : F.obj (Opposite.op T)) :
    yonedaEquiv.symm (α.app (Opposite.op T) x) = yonedaEquiv.symm x ≫ α := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]

/-! ### Representability from a finite locally free étale relation -/

/-- The two projections of the self base change of a morphism are interchanged by the symmetry
isomorphism of the fibre product, so one is finite locally free as soon as the other is. -/
private theorem isFiniteLocallyFree_map_fst'_self
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} {ψ : yoneda.obj V ⟶ Z}
    (hrep : yoneda.relativelyRepresentable ψ)
    (hs : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map (hrep.snd ψ))) :
    IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map (hrep.fst' ψ)) := by
  have he : (BigFppfOver.toScheme B S hS).map (hrep.symmetry hrep) ≫
      (BigFppfOver.toScheme B S hS).map (hrep.snd ψ) =
      (BigFppfOver.toScheme B S hS).map (hrep.fst' ψ) := by
    rw [← Functor.map_comp, hrep.symmetry_snd hrep]
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree.{u}) _ _ hs

/-- **An algebraic space with a surjective étale chart whose relation is finite locally free is a
scheme.** Let `ψ : h_V ⟶ Z` be a surjective étale chart of an algebraic space over `S` and let the
self base change of `ψ` — the relation `R = V ×_Z V` — be finite locally free. If moreover every
finite set of points of `V` lies in an affine open, then `Z` is representable. -/
theorem isRepresentable_of_presheafSurjective_presheafEtale_of_isFiniteLocallyFree_relation
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ Z)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hflf : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd ψ)))
    (haffine : ∀ E : Set ((BigFppfOver.toScheme B S hS).obj V), E.Finite →
      ∃ O : ((BigFppfOver.toScheme B S hS).obj V).Opens, IsAffineOpen O ∧ E ⊆ O) :
    Z.IsRepresentable := by
  classical
  let _ : EssentiallySmall.{u} (BigFppfOver B S hS) :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 B.Schemes) (B.obj hS)))
  let _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} (BigFppfOver.topology B S hS) _
  set hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ with hrepdef
  set t : hrep.pullback ψ ⟶ V := hrep.fst' ψ with htdef
  set s : hrep.pullback ψ ⟶ V := hrep.snd ψ with hsdef
  have hR : IsPullback (yoneda.map t) (yoneda.map s) ψ ψ := hrep.isPullback' ψ
  have hflft : IsFiniteLocallyFree
      (((Over.post (X := B.obj hS) B.inclusion).map t).left) :=
    isFiniteLocallyFree_map_fst'_self B S hS hrep hflf
  have hflfs : IsFiniteLocallyFree
      (((Over.post (X := B.obj hS) B.inclusion).map s).left) := hflf
  have haffine' : ∀ E : Set (((Over.post (X := B.obj hS) B.inclusion).obj V).left), E.Finite →
      ∃ O : (((Over.post (X := B.obj hS) B.inclusion).obj V).left).Opens,
        IsAffineOpen O ∧ E ⊆ O := haffine
  obtain ⟨M, π, hsize, hflfπ, hsurjπ, hpbπ⟩ :=
    GroupoidScheme.exists_schemeQuotient_of_isFiniteLocallyFree_relation B S hS
      ((Over.post (X := B.obj hS) B.inclusion).map t)
      ((Over.post (X := B.obj hS) B.inclusion).map s) hflft hflfs
      (isEquivalenceRelation_of_isPullback B S hS ψ t s hR) V.left.2 haffine'
  have hM : B.Contains M.left := lt_of_le_of_lt hsize V.left.2
  set U' : BigFppfOver B S hS := Over.mk (⟨M.hom⟩ : B.obj hM ⟶ B.obj hS) with hU'def
  obtain ⟨m, d, hmπ, hmono, hfd⟩ :=
    exists_mono_yoneda_of_isPullback B S hS hZ.isSheaf ψ t s hR (U' := U') π
      (IsFiniteLocallyFree.flat π.left) (IsFiniteLocallyFree.locallyOfFinitePresentation π.left)
      hsurjπ hpbπ
  have hts : t ≫ m = s ≫ m := by
    refine (Over.post (X := B.obj hS) B.inclusion).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hmπ]
    exact hpbπ.w
  obtain ⟨hRsh, hUsh, hcolim⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS ψ t s hR hZ hsurj hetale
  obtain ⟨hcolim⟩ := hcolim
  set J := BigFppfOver.topology B S hS with hJdef
  let RF : Sheaf J (Type u) := ⟨yoneda.obj (hrep.pullback ψ), hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj V, hUsh⟩
  let MF : Sheaf J (Type u) := ⟨yoneda.obj U', isSheaf_yoneda_obj B S hS U'⟩
  let ZF : Sheaf J (Type u) := ⟨Z, hZ.isSheaf⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let ff : UF ⟶ ZF := ⟨ψ⟩
  let mf : UF ⟶ MF := ⟨yoneda.map m⟩
  let dS : MF ⟶ ZF := ⟨d⟩
  have hwm : tf ≫ mf = sf ≫ mf := by
    refine Sheaf.hom_ext ?_
    change yoneda.map t ≫ yoneda.map m = yoneda.map s ≫ yoneda.map m
    rw [← Functor.map_comp, ← Functor.map_comp, hts]
  have hwf : tf ≫ ff = sf ≫ ff := Sheaf.hom_ext hR.w
  have hcolim' : IsColimit (Cofork.ofπ ff hwf) := hcolim
  set c := hcolim'.desc (Cofork.ofπ mf hwm) with hcdef
  have hc : ff ≫ c = mf := by
    simpa only [Cofork.π_ofπ] using
      Cofork.IsColimit.π_desc (t := Cofork.ofπ mf hwm) hcolim'
  have hmd : mf ≫ dS = ff := Sheaf.hom_ext hfd
  have hsplit : c ≫ dS = 𝟙 ZF := by
    refine Cofork.IsColimit.hom_ext hcolim' ?_
    simp only [Cofork.π_ofπ, ← Category.assoc, hc, hmd]
    exact (Category.comp_id ff).symm
  have hsplit' : c.hom ≫ d = 𝟙 Z := Sheaf.hom_ext_iff.mp hsplit
  have _ : Mono d := hmono
  have _ : IsSplitEpi d := IsSplitEpi.mk' ⟨c.hom, hsplit'⟩
  have _ : IsIso d := isIso_of_mono_of_isSplitEpi d
  exact Functor.IsRepresentable.mk' (asIso d)

/-! ### The dense schematic locus of a space with a bounded affine chart -/

/-- **The schematic locus is dense for a space with a bounded affine chart.** Let `X` be an
algebraic space over a scheme `S` admitting a surjective étale chart `φ : h_U ⟶ X` by an affine
scheme whose fibres are universally bounded in the sense of Stacks 03JL. Then `X` has a
representable open subspace whose point set is dense: the conclusion of Stacks 03JI. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_boundedAffineChart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (φ : yoneda.obj U ⟶ X)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hbdd : HasUniversallyBoundedFibers B S hS U φ) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  have _ := hU
  refine exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace B S hS hX ?_
  intro G hG hGne
  obtain ⟨Y, d, -, -, hYopen, hYdeg, hmeet, hmiss⟩ :=
    exists_max_degree_stratum_of_hasUniversallyBounded B S hS hX φ
      (isFlat_of_presheafEtale B S hS hetale)
      (isLocallyOfFinitePresentation_of_presheafEtale B S hS hetale)
      (isSeparated_of_scheme_isSeparated B S hS inferInstance φ)
      (isLocallyQuasiFinite_of_presheafEtale B S hS hetale) hbdd
      (Set.range (pointsMap B S hS G.toFunctor G.ι)) hGne
  set W : Set (points B S hS X) :=
    Set.range (pointsMap B S hS G.toFunctor G.ι) ∩
      Set.range (pointsMap B S hS (Y d).toFunctor (Y d).ι) with hWdef
  have hWopen : IsOpen W :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2).inter
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS (Y d).ι (hYopen d).2)
  set Z := openSubspaceOfPoints B S hS X W with hZdef
  have hZopen : IsOpenSubspace B S hS Z :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX W hWopen
  have hZpts : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = W :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS W
  obtain ⟨V, i, ψ, hi, hpb, hψsurj, hψetale⟩ :=
    exists_chart_openSubspaceOfPoints B S hS φ hsurj hetale W hWopen
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) := hi
  have hrank : ∀ p : FieldValuedPoint B S hS Z.toFunctor,
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZopen.1 ψ).snd
          (yonedaEquiv.symm p.value))) d := by
    intro p
    set q := FieldValuedPoint.map B S hS Z.toFunctor Z.ι p with hqdef
    have hqval : yonedaEquiv.symm q.value = yonedaEquiv.symm p.value ≫ Z.ι :=
      yonedaEquiv_symm_app B S hS Z.ι p.value
    have hqmem : q.class B S hS X ∈ W := by
      rw [hqdef, ← pointsMap_class, ← hZpts]
      exact ⟨p.class B S hS Z.toFunctor, rfl⟩
    have hfactor : ∀ e : ℕ, IsOpenSubspace B S hS (Y e) →
        ((∃ g : yoneda.obj q.siteObject ⟶ (Y e).toFunctor,
            g ≫ (Y e).ι = yonedaEquiv.symm q.value) ↔
          q.class B S hS X ∈ Set.range (pointsMap B S hS (Y e).toFunctor (Y e).ι)) := by
      intro e he
      rw [factorsThrough_openSubspace_iff_points B S hS hX
          (isAlgebraicSpace_yoneda B S hS q.siteObject) (Y e) he (yonedaEquiv.symm q.value),
        range_pointsMap_yonedaEquiv_symm B S hS q, Set.singleton_subset_iff]
    have hd1 : ¬ (∃ g : yoneda.obj q.siteObject ⟶ (Y (d + 1)).toFunctor,
        g ≫ (Y (d + 1)).ι = yonedaEquiv.symm q.value) := by
      intro hex
      have := (hfactor (d + 1) (hYopen (d + 1))).1 hex
      exact Set.eq_empty_iff_forall_notMem.1 hmiss (q.class B S hS X) ⟨hqmem.1, this⟩
    have hrankq := isFiniteLocallyFreeOfRank_map_snd_fieldMorphism_of_degree_eq B S hS hX φ d q
      ((hYdeg d q).1 ((hfactor d (hYopen d)).2 hqmem.2))
      (fun h => hd1 ((hYdeg (d + 1) q).2 h))
    refine (property_map_snd_of_isPullback B S hS (IsFiniteLocallyFreeOfRank.property.{u} d)
      (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ)
      (relativelyRepresentable_of_isAlgebraicSpace B S hS hZopen.1 ψ) hpb
      (yonedaEquiv.symm p.value)).2 ?_
    rw [← hqval]
    exact hrankq
  have hVsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj V) := by
    refine ⟨?_⟩
    rw [show Limits.terminal.from ((BigFppfOver.toScheme B S hS).obj V) =
        (BigFppfOver.toScheme B S hS).map i ≫
          Limits.terminal.from ((BigFppfOver.toScheme B S hS).obj U) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hZrep : Z.toFunctor.IsRepresentable :=
    isRepresentable_of_presheafSurjective_presheafEtale_of_isFiniteLocallyFree_relation
      B S hS hZopen.1 ψ hψsurj hψetale
      (isFiniteLocallyFree_map_snd_self_of_isSeparated_scheme B S hS hZopen.1 ψ hψetale
        hVsep d hrank)
      (fun E hE => exists_affineOpen_containing_finite_of_isOpenImmersion_isAffine
        ((BigFppfOver.toScheme B S hS).map i) hE)
  refine ⟨Z, le_of_range_pointsMap_ι_subset B S hS hG ?_, hZopen, hZrep, ?_⟩
  · rw [hZpts]
    exact Set.inter_subset_left
  · rw [hZpts]
    exact hmeet

end AlgebraicGeometry.Space

end
