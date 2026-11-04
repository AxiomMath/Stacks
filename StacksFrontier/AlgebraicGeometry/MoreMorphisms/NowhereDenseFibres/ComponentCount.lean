module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.CoveringFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingHypotheses
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseGenericFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Irreducible components in fibres near the generic point

Let `f : X ⟶ Y` be a finite type morphism and let `η` be a generic point of `Y`. If the
generic fibre has `n` irreducible components, then every fibre over some nonempty open subset
of `Y` has at least `n` irreducible components. This is Stacks Tag 0554.

## Main results

* `AlgebraicGeometry.exists_open_ncard_irreducibleComponents_fiber_ge` is Stacks Tag 0554.
* `AlgebraicGeometry.irreducibleComponentsLowerBoundAfterShrinking` discharges the
  hypothesis `AlgebraicGeometry.IrreducibleComponentsLowerBoundAfterShrinking` carried by the
  results of the Tag 055A chain.
* `AlgebraicGeometry.componentClosureSubscheme` is the reduced closed subscheme cut out by the
  closure of a subset of the generic fibre, and
  `AlgebraicGeometry.componentClosure_exists_open_image` says that it meets every fibre over a
  neighbourhood of the generic point.

## Implementation notes

Being of finite type is expressed by `LocallyOfFiniteType` together with `QuasiCompact`, and
a chosen dense generic point by `IsGenericPoint η Set.univ`, which already forces the target
to be irreducible. The number of components is the `Set.ncard` of `irreducibleComponents`;
the fibres are of finite type over fields, hence Noetherian, so this is their actual
cardinality. For each irreducible component of the generic fibre the proof takes the reduced
closed subscheme of `X` cut out by the closure of that component. Over a suitable open subset
of the base these subschemes cover the fibres, each of them meets the fibre, and by Tag 054X
the intersections with the other subschemes are nowhere dense in it; this exhibits `n`
distinct irreducible components in the fibre.

## References

* [Stacks Project, Tag 0554](https://stacks.math.columbia.edu/tag/0554)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The reduced closed subscheme of `X` cut out by the closure of the image of a subset of
the fibre of `f` over `η`. -/
noncomputable def componentClosureSubscheme {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : Set (f.fiber η)) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure (f.fiberι η '' C), isClosed_closure⟩

/-- The support of `componentClosureSubscheme f η C` is the closure of the image of `C`. -/
theorem componentClosureSubscheme_support {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : Set (f.fiber η)) :
    (componentClosureSubscheme f η C).support = closure (f.fiberι η '' C) := by
  simp [componentClosureSubscheme, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The inclusion of the reduction of a scheme is a homeomorphism. -/
private theorem isHomeomorph_nilradical_subschemeι (Y : Scheme.{u}) :
    IsHomeomorph Y.nilradical.subschemeι :=
  (universalHomeomorphism_nilradical_subschemeι Y).universally_isHomeomorph _ _ _
    IsPullback.of_id_snd

/-- The canonical factorization of `I.subschemeι ≫ f` through the reduction of `Y`, available
because `I.subscheme` is reduced. -/
private noncomputable def componentClosureMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : X.IdealSheafData) [IsReduced I.subscheme] : I.subscheme ⟶ Y.nilradical.subscheme :=
  Classical.choose (Scheme.existsUnique_lift_nilradical_subschemeι (I.subschemeι ≫ f))

private theorem componentClosureMap_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : X.IdealSheafData) [IsReduced I.subscheme] :
    componentClosureMap f I ≫ Y.nilradical.subschemeι = I.subschemeι ≫ f :=
  (Classical.choose_spec
    (Scheme.existsUnique_lift_nilradical_subschemeι (I.subschemeι ≫ f))).1

private theorem componentClosureMap_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (I : X.IdealSheafData) [IsReduced I.subscheme] :
    LocallyOfFiniteType (componentClosureMap f I) := by
  have hcomp : LocallyOfFiniteType (componentClosureMap f I ≫ Y.nilradical.subschemeι) := by
    rw [componentClosureMap_fac]
    infer_instance
  exact locallyOfFiniteType_of_comp (componentClosureMap f I) Y.nilradical.subschemeι

private theorem componentClosureMap_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (I : X.IdealSheafData) [IsReduced I.subscheme] :
    QuasiCompact (componentClosureMap f I) := by
  let r := Y.nilradical.subschemeι
  have hr : IsHomeomorph r := isHomeomorph_nilradical_subschemeι Y
  have htotal : QuasiCompact (componentClosureMap f I ≫ r) := by
    rw [componentClosureMap_fac]
    infer_instance
  constructor
  intro U hU hcompact
  have heq : (componentClosureMap f I) ⁻¹' U = (componentClosureMap f I ≫ r) ⁻¹' (r '' U) := by
    ext x
    refine ⟨fun hx => ⟨componentClosureMap f I x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, hxy⟩
    change r y = r (componentClosureMap f I x) at hxy
    simpa [hr.injective hxy] using hy
  rw [heq]
  exact htotal.isCompact_preimage (r '' U) (hr.isOpenMap _ hU) (hcompact.image hr.continuous)

/-- Generic flatness for the canonical map to the reduction of the base. -/
private theorem componentClosure_denseFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData)
    [IsReduced I.subscheme] :
    ∃ U : Y.nilradical.subscheme.Opens, Dense (U : Set Y.nilradical.subscheme) ∧
      Flat ((componentClosureMap f I).resLE U ((componentClosureMap f I) ⁻¹ᵁ U) le_rfl) ∧
      FinitePresentation
        ((componentClosureMap f I).resLE U ((componentClosureMap f I) ⁻¹ᵁ U) le_rfl) := by
  have : LocallyOfFiniteType (componentClosureMap f I) :=
    componentClosureMap_locallyOfFiniteType f I
  have : QuasiCompact (componentClosureMap f I) := componentClosureMap_quasiCompact f I
  have : IsReduced Y.nilradical.subscheme := isReduced_nilradical_subscheme Y
  let F : I.subscheme.Modules := SheafOfModules.unit _
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit I.subscheme
  have : F.IsFiniteType := structureSheaf_isFiniteType I.subscheme
  obtain ⟨U, hU, hflat, hfin, -, -⟩ :=
    exists_dense_open_flat_finitePresentation (componentClosureMap f I) F
  exact ⟨U, hU, hflat, hfin⟩

/-- The fibres of a finite type morphism are Noetherian. -/
theorem fiber_isNoetherian {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] (y : Y) : IsNoetherian (f.fiber y) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    show LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  have : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  exact ⟨⟩

/-- If a closed subscheme of `X` meets the fibre over the generic point, then it meets the
fibre over every point of some open neighbourhood of the generic point. -/
theorem componentClosure_exists_open_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData) [IsReduced I.subscheme]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hηI : ∃ x : I.subscheme, (I.subschemeι ≫ f) x = η) :
    ∃ V : Set Y, IsOpen V ∧ η ∈ V ∧
      ∀ y ∈ V, ∃ x : I.subscheme, (I.subschemeι ≫ f) x = y := by
  classical
  let r := Y.nilradical.subschemeι
  have hr : IsHomeomorph r := isHomeomorph_nilradical_subschemeι Y
  let eRed : Y.nilradical.subscheme ≃ₜ Y :=
    hr.isEmbedding.toHomeomorphOfSurjective hr.surjective
  have : Nonempty Y.nilradical.subscheme := ⟨eRed.symm η⟩
  have : IsReduced Y.nilradical.subscheme := isReduced_nilradical_subscheme Y
  let g := componentClosureMap f I
  obtain ⟨U, hU, hflat, hfin⟩ := componentClosure_denseFlat f I
  have : Flat (g.resLE U (g ⁻¹ᵁ U) le_rfl) := hflat
  have : LocallyOfFinitePresentation (g.resLE U (g ⁻¹ᵁ U) le_rfl) :=
    hfin.locallyOfFinitePresentation
  let η' : Y.nilradical.subscheme := eRed.symm η
  have hη' : IsGenericPoint η' (Set.univ : Set Y.nilradical.subscheme) := by
    simpa [η'] using hη.image eRed.symm.continuous
  have hη'U : η' ∈ U := by
    refine (hη'.mem_open_set_iff U.2).2 ?_
    obtain ⟨z, hz⟩ := hU.nonempty
    exact ⟨z, trivial, hz⟩
  have hηI' : ∃ x : I.subscheme, g x = η' := by
    obtain ⟨x, hx⟩ := hηI
    have hred : eRed (g x) = η := by
      show r (g x) = η
      rw [← Scheme.Hom.comp_apply, componentClosureMap_fac]
      exact hx
    exact ⟨x, eRed.injective (by simpa [η'] using hred)⟩
  let q := g.resLE U (g ⁻¹ᵁ U) le_rfl ≫ U.ι
  have hqOpen : IsOpenMap q :=
    (U.ι).isOpenMap.comp (g.resLE U (g ⁻¹ᵁ U) le_rfl).isOpenMap
  have q_apply (x : g ⁻¹ᵁ U) : q x = g x.1 := Scheme.Hom.coe_resLE_apply g le_rfl x
  have hqRange : IsOpen (Set.range q) := by
    simpa [Set.image_univ] using hqOpen Set.univ isOpen_univ
  have hη'q : η' ∈ Set.range q := by
    obtain ⟨x, hx⟩ := hηI'
    have hxU : x ∈ g ⁻¹ᵁ U := by
      show g x ∈ U
      rw [hx]
      exact hη'U
    exact ⟨⟨x, hxU⟩, (q_apply ⟨x, hxU⟩).trans hx⟩
  refine ⟨eRed '' Set.range q, eRed.isOpenMap _ hqRange, ⟨η', hη'q, by simp [η']⟩, ?_⟩
  rintro y ⟨z, ⟨x, hx⟩, hzy⟩
  refine ⟨x.1, ?_⟩
  have hcomp : (componentClosureMap f I ≫ r) x.1 = y := by
    have hzy' : eRed (q x) = y := by rwa [hx]
    rw [q_apply x] at hzy'
    rw [Scheme.Hom.comp_apply]
    exact hzy'
  rwa [componentClosureMap_fac] at hcomp

/-- Compatibility of `fiberMapComp` with the inclusions of the fibres. -/
private theorem fiberι_fiberMapComp_apply {X Y Z : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y) (y : Y)
    (z : (g ≫ f).fiber y) : f.fiberι y (g.fiberMapComp f y z) = g ((g ≫ f).fiberι y z) := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun k => k z) (Scheme.Hom.fiberMapComp_fiberι g f y)

/-- A closed subset of the generic fibre is recovered as the part of that fibre lying in the
support of the closed subscheme it cuts out. -/
theorem componentClosureSubscheme_preimage_support {X Y : Scheme.{u}} (f : X ⟶ Y)
    (η : Y) (C : Set (f.fiber η)) (hC : IsClosed C) :
    (f.fiberι η) ⁻¹' (componentClosureSubscheme f η C).support = C := by
  rw [componentClosureSubscheme_support,
    ← (f.fiberι η).isEmbedding.closure_eq_preimage_closure_image, hC.closure_eq]

private theorem componentClosure_support_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : Set (f.fiber η)) (hC : IsClosed C) (x : f.fiber η) :
    f.fiberι η x ∈ (componentClosureSubscheme f η C).support ↔ x ∈ C :=
  Set.ext_iff.mp (componentClosureSubscheme_preimage_support f η C hC) x

/-- The generic fibre of the subscheme cut out by a closed subset of the generic fibre is
that closed subset. -/
private theorem range_fiberMapComp_componentClosureSubscheme {X Y : Scheme.{u}} (f : X ⟶ Y)
    (η : Y) (C : Set (f.fiber η)) (hC : IsClosed C) :
    Set.range (Scheme.Hom.fiberMapComp (componentClosureSubscheme f η C).subschemeι f η) =
      C := by
  classical
  let I := componentClosureSubscheme f η C
  have hsupport : (f.fiberι η) ⁻¹' (I.support : Set X) = C :=
    componentClosureSubscheme_preimage_support f η C hC
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨z, rfl⟩
    have hz : I.subschemeι ((I.subschemeι ≫ f).fiberι η z) ∈ (I.support : Set X) := by
      rw [← I.range_subschemeι]
      exact ⟨(I.subschemeι ≫ f).fiberι η z, rfl⟩
    have hpre : Scheme.Hom.fiberMapComp I.subschemeι f η z ∈
        (f.fiberι η) ⁻¹' (I.support : Set X) := by
      show f.fiberι η _ ∈ (I.support : Set X)
      rw [fiberι_fiberMapComp_apply]
      exact hz
    rwa [hsupport] at hpre
  · have hx' : x ∈ (f.fiberι η) ⁻¹' (I.support : Set X) := by
      rw [hsupport]
      exact hx
    have hmem : f.fiberι η x ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hx'
    obtain ⟨z, hz⟩ := hmem
    have hzbase : (I.subschemeι ≫ f) z = η := by
      rw [Scheme.Hom.comp_apply, hz]
      exact Scheme.Hom.apply_fiberι f η x
    refine ⟨((I.subschemeι ≫ f).fiberHomeo η).symm ⟨z, hzbase⟩, ?_⟩
    refine (f.fiberι η).isEmbedding.injective ?_
    rw [fiberι_fiberMapComp_apply, (I.subschemeι ≫ f).fiberι_fiberHomeo_symm η ⟨z, hzbase⟩]
    exact hz

/-- **Stacks Project, Tag 0554.** For a finite type morphism to a scheme with a chosen dense
generic point, the number of irreducible components of the fibres is at least the number for
the generic fibre over a nonempty open subset of the base. -/
@[stacks 0554, ega "IV 9.7.1" "irreducible components"]
theorem exists_open_ncard_irreducibleComponents_fiber_ge {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y) (hη : IsGenericPoint η Set.univ)
    (n : ℕ) (hcomp : (irreducibleComponents (f.fiber η)).ncard = n) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, n ≤ (irreducibleComponents (f.fiber y)).ncard := by
  classical
  by_cases hn : n = 0
  · exact ⟨Set.univ, isOpen_univ, ⟨η, Set.mem_univ _⟩, fun y _ => hn ▸ Nat.zero_le _⟩
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).2 hη.isIrreducible
  have : IsNoetherian (f.fiber η) := fiber_isNoetherian f η
  let : Fintype (irreducibleComponents (f.fiber η)) :=
    (NoetherianSpace.finite_irreducibleComponents (α := f.fiber η)).fintype
  have hcard : Fintype.card (irreducibleComponents (f.fiber η)) = n := by simpa using hcomp
  let e : Fin n ≃ irreducibleComponents (f.fiber η) := (Fintype.equivFinOfCardEq hcard).symm
  let C : Fin n → Set (f.fiber η) := fun i => (e i).val
  have hCmem (i : Fin n) : C i ∈ irreducibleComponents (f.fiber η) := (e i).property
  have hCclosed (i : Fin n) : IsClosed (C i) :=
    isClosed_of_mem_irreducibleComponents (C i) (hCmem i)
  have hcoverη : ∀ x : f.fiber η, ∃ i : Fin n, x ∈ C i := by
    intro x
    have hx : x ∈ ⋃₀ irreducibleComponents (f.fiber η) := by
      rw [sUnion_irreducibleComponents]
      trivial
    obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp hx
    exact ⟨e.symm ⟨D, hD⟩, by simpa [C] using hxD⟩
  let I : Fin n → X.IdealSheafData := fun i => componentClosureSubscheme f η (C i)
  have hIred (i : Fin n) : IsReduced (I i).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
      (⟨closure (f.fiberι η '' C i), isClosed_closure⟩ : Closeds X)
  have hOpenImage : ∀ i : Fin n, ∃ V : Set Y, IsOpen V ∧ η ∈ V ∧
      ∀ y ∈ V, ∃ x : (I i).subscheme, ((I i).subschemeι ≫ f) x = y := by
    intro i
    let := hIred i
    refine componentClosure_exists_open_image f (I i) η hη ?_
    obtain ⟨c, hc⟩ := (hCmem i).1.nonempty
    have hrange : f.fiberι η c ∈ Set.range (I i).subschemeι := by
      rw [(I i).range_subschemeι]
      exact (componentClosure_support_iff f η (C i) (hCclosed i) c).2 hc
    obtain ⟨x, hx⟩ := hrange
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, hx]
    exact Scheme.Hom.apply_fiberι f η c
  have hOpenBad : ∀ i : Fin n, ∃ V : Set Y, IsOpen V ∧ η ∈ V ∧ ∀ y ∈ V,
      IsNowhereDense (((I i).subschemeι ≫ f).fiberι y ⁻¹'
        ((I i).subschemeι ⁻¹' ⋃ j ∈ Finset.univ.erase i, (I j).support)) := by
    intro i
    let := hIred i
    let g := (I i).subschemeι ≫ f
    have : LocallyOfFiniteType g := inferInstance
    have : QuasiCompact g := inferInstance
    let D : Set X := ⋃ j ∈ Finset.univ.erase i, (I j).support
    let Z : Set (I i).subscheme := (I i).subschemeι ⁻¹' D
    have hZclosed : IsClosed Z :=
      ((Finset.univ.erase i).finite_toSet.isClosed_biUnion
        (fun j _ => (I j).support.2)).preimage (I i).subschemeι.continuous
    have hrange : Set.range (Scheme.Hom.fiberMapComp (I i).subschemeι f η) = C i :=
      range_fiberMapComp_componentClosureSubscheme f η (C i) (hCclosed i)
    let eI : g.fiber η ≃ₜ ↥(C i) :=
      (Scheme.Hom.fiberMapComp (I i).subschemeι f η).isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr hrange)
    let Dη : Set (f.fiber η) := ⋃ j ∈ Finset.univ.erase i, C j
    let Bη : Set (↥(C i)) := (Subtype.val : C i → f.fiber η) ⁻¹' Dη
    have hBηproper : Bη ≠ Set.univ := by
      intro hall
      have hcover : C i ⊆ ⋃ j ∈ Finset.univ.erase i, C j := fun x hx => by
        have hxB : (⟨x, hx⟩ : C i) ∈ Bη := by rw [hall]; trivial
        exact hxB
      obtain ⟨t, ht, hsub⟩ :=
        isIrreducible_iff_sUnion_isClosed.mp (hCmem i).1 ((Finset.univ.erase i).image C)
          (by
            intro z hz
            simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ] at hz
            obtain ⟨j, _, rfl⟩ := hz
            exact hCclosed j)
          (fun x hx => by
            obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hcover hx)
            exact Set.mem_sUnion.mpr ⟨C j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, hxj⟩)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_erase.mp hj).1
        (e.injective (Subtype.ext (Set.Subset.antisymm ((hCmem i).2 (hCmem j).1 hsub) hsub)))
    have hbadSource : IsNowhereDense (eI ⁻¹' Bη) :=
      (eI.isNowhereDense_preimage_iff Bη).mpr
        (isNowhereDense_of_isClosed_ne_univ_subtype (C i) (hCmem i).1 Bη
          (((Finset.univ.erase i).finite_toSet.isClosed_biUnion
            fun j _ => hCclosed j).preimage continuous_subtype_val) hBηproper)
    have hgeneric : (g.fiberι η) ⁻¹' Z = eI ⁻¹' Bη := by
      ext z
      show ((I i).subschemeι (g.fiberι η z) ∈ D) ↔ ((eI z : f.fiber η) ∈ Dη)
      have heval : (eI z : f.fiber η) = Scheme.Hom.fiberMapComp (I i).subschemeι f η z := rfl
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.mp hz
        rw [heval]
        refine Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
        refine (componentClosure_support_iff f η (C j) (hCclosed j) _).mp ?_
        rw [fiberι_fiberMapComp_apply]
        exact hzj
      · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.mp hz
        have hsupport := (componentClosure_support_iff f η (C j) (hCclosed j)
          (Scheme.Hom.fiberMapComp (I i).subschemeι f η z)).2 (by simpa [heval] using hzj)
        rw [fiberι_fiberMapComp_apply] at hsupport
        exact Set.mem_iUnion₂.mpr ⟨j, hj, hsupport⟩
    obtain ⟨V, hVopen, hVne, hVnd⟩ := exists_open_isNowhereDense_fiber g (Z := Z) hZclosed η
      hη (by rw [hgeneric]; exact hbadSource)
    obtain ⟨z, hz⟩ := hVne
    exact ⟨V, hVopen, (hη.mem_open_set_iff hVopen).2 ⟨z, trivial, hz⟩, hVnd⟩
  choose Vimage hVimage using hOpenImage
  choose Vbad hVbad using hOpenBad
  obtain ⟨Vcover, hVcoverOpen, ⟨z, hz⟩, hVcover⟩ :=
    exists_open_fiber_covered_by_closures f η hη C hcoverη
  refine ⟨Vcover ∩ ⋂ i : Fin n, Vimage i ∩ Vbad i,
    hVcoverOpen.inter (isOpen_iInter_of_finite fun i => (hVimage i).1.inter (hVbad i).1),
    ⟨η, (hη.mem_open_set_iff hVcoverOpen).2 ⟨z, trivial, hz⟩,
      Set.mem_iInter.mpr fun i => ⟨(hVimage i).2.1, (hVbad i).2.1⟩⟩, ?_⟩
  intro y hy
  let S : Fin n → Set (f.fiber y) := fun i => (f.fiberι y) ⁻¹' ((I i).support : Set X)
  have hSclosed (i : Fin n) : IsClosed (S i) :=
    ((I i).support.2).preimage (f.fiberι y).continuous
  have hScover : ∀ x : f.fiber y, ∃ i, x ∈ S i := by
    intro x
    obtain ⟨i, hi⟩ := hVcover y hy.1 x
    exact ⟨i, (componentClosureSubscheme_support f η (C i)).ge hi⟩
  have hSexclusive : ∀ i, ∃ x, x ∈ S i ∧ ∀ j, j ≠ i → x ∉ S j := by
    intro i
    have hyi : y ∈ Vimage i ∩ Vbad i := Set.mem_iInter.mp hy.2 i
    obtain ⟨w, hw⟩ := (hVimage i).2.2 y hyi.1
    let g := (I i).subschemeι ≫ f
    let Z : Set (I i).subscheme :=
      (I i).subschemeι ⁻¹' ⋃ j ∈ Finset.univ.erase i, (I j).support
    have hnd : IsNowhereDense ((g.fiberι y) ⁻¹' Z) := (hVbad i).2.2 y hyi.2
    have hbadproper : ((g.fiberι y) ⁻¹' Z) ≠ Set.univ := by
      intro hall
      rw [IsNowhereDense, hall, closure_univ, interior_univ] at hnd
      exact (hnd ▸ Set.mem_univ ((g.fiberHomeo y).symm ⟨w, hw⟩) :
        ((g.fiberHomeo y).symm ⟨w, hw⟩ : g.fiber y) ∈ (∅ : Set (g.fiber y)))
    obtain ⟨z', hz'⟩ := Set.nonempty_compl.mpr hbadproper
    have hfac := fiberι_fiberMapComp_apply (I i).subschemeι f y z'
    refine ⟨Scheme.Hom.fiberMapComp (I i).subschemeι f y z', ?_, fun j hji hxj => hz' ?_⟩
    · show f.fiberι y _ ∈ ((I i).support : Set X)
      rw [hfac, ← (I i).range_subschemeι]
      exact ⟨g.fiberι y z', rfl⟩
    · show (I i).subschemeι (g.fiberι y z') ∈ ⋃ j ∈ Finset.univ.erase i, (I j).support
      rw [← hfac]
      exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, hxj⟩
  have : IsNoetherian (f.fiber y) := fiber_isNoetherian f y
  exact le_ncard_irreducibleComponents_of_isClosed_cover n S hSclosed hScover hSexclusive

/-- Stacks Tag 0554 discharges the hypothesis
`AlgebraicGeometry.IrreducibleComponentsLowerBoundAfterShrinking`. -/
theorem irreducibleComponentsLowerBoundAfterShrinking :
    IrreducibleComponentsLowerBoundAfterShrinking.{u} :=
  fun f _ _ η hη n hn => exists_open_ncard_irreducibleComponents_fiber_ge f η hη n hn

end AlgebraicGeometry

end
