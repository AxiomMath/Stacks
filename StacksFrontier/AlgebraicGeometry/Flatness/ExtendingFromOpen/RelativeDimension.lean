module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.Flat.Finiteness
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Specialization.Defs

/-!
# Relative dimension over a dense open subscheme

A flat morphism locally of finite type whose relative dimension is bounded by `e` over a dense
open subscheme of the base has the same bound everywhere, provided either the morphism is locally
of finite presentation or the open is retrocompact.

In the finitely presented case the source is covered, up to a fibrewise dense open, by open
pieces of constant relative dimension. Flatness makes the morphism open, so a piece of relative
dimension `d` has open image meeting the dense open, and comparing fibre dimensions across the
base change to that open gives `d ≤ e`. The bound at an arbitrary point then follows because the
local dimension of a fibre is attained on an irreducible component, whose generic point lies in
every fibrewise dense open.

The retrocompact case is reduced to the first one by base changing to a valuation ring mapping
into the base: over a valuation ring a flat morphism locally of finite type is automatically
locally of finite presentation.

## Main results

* `AlgebraicGeometry.relativeDimensionLE_of_dense_open` extends a relative-dimension bound from a
  dense open subscheme of the base.

## Implementation notes

The restriction of `f` to an open `U` of the base is written as the base-change morphism
`CategoryTheory.Limits.pullback.snd f U.ι`, and the two alternative finiteness assumptions of the
source are kept as a disjunction. The valuation ring used in the retrocompact case is produced by
`AlgebraicGeometry.exists_valuationRing_of_image_point`, whose target is the scheme-theoretic
image of the open immersion; density of the open makes every point of the base such an image
point.

## References

* [Stacks Project, Tag 081L](https://stacks.math.columbia.edu/tag/081L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The local dimension of a scheme locally of finite type over a field at the generic point of
an irreducible component is the dimension of that component. -/
private theorem topologicalKrullDimAt_eq_topologicalKrullDim_of_closure_eq
    (k : Type u) [Field k] (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {Z : Set Y} (hZ : Z ∈ irreducibleComponents Y)
    {η : Y} (hη : closure ({η} : Set Y) = Z) :
    topologicalKrullDimAt Y η = topologicalKrullDim Z := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y q η]
  refine le_antisymm (iSup_le fun W => iSup_le fun hW => ?_) ?_
  · have hZW : Z ⊆ W := by
      rw [← hη]
      exact closure_minimal (Set.singleton_subset_iff.mpr hW.2)
        (isClosed_of_mem_irreducibleComponents W hW.1)
    rw [Set.Subset.antisymm (hZ.2 hW.1.1 hZW) hZW]
  · exact le_iSup_of_le Z (le_iSup_of_le ⟨hZ, hη ▸ subset_closure (Set.mem_singleton η)⟩ le_rfl)

/-- Transporting a point of a fibre along an equality of base points does not change the local
dimension of the fibre at it. -/
private theorem topologicalKrullDimAt_fiber_cast {X S : Scheme.{u}} (f : X ⟶ S) {s t : S}
    (h : s = t) (y : f.fiber s) :
    topologicalKrullDimAt (f.fiber t) (h ▸ y) = topologicalKrullDimAt (f.fiber s) y := by
  cases h
  rfl

/-- If the range of a morphism is dense then every point of the target is the image of a point of
its scheme-theoretic image. -/
private theorem exists_imageι_eq_of_denseRange {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Dense (Set.range f)) (s : S) : ∃ z : f.image, f.imageι z = s := by
  have hsub : Set.range f ⊆ Set.range f.imageι := by
    rintro y ⟨x, rfl⟩
    refine ⟨f.toImage x, ?_⟩
    have h := congrArg (fun k : X ⟶ S => k x) (Scheme.Hom.toImage_imageι f)
    simpa only [Scheme.Hom.comp_apply] using h
  have hall : Set.univ ⊆ Set.range f.imageι :=
    calc
      Set.univ = closure (Set.range f) := hf.closure_eq.symm
      _ ⊆ closure (Set.range f.imageι) := closure_mono hsub
      _ = Set.range f.imageι := f.imageι.isClosedEmbedding.isClosed_range.closure_eq
  exact hall (Set.mem_univ s)

/-- **Stacks Project, Tag 053E over a scheme.** A flat morphism locally of finite type whose base
is the spectrum of a valuation ring is locally of finite presentation. The property is checked on
an affine cover of the source, where it is Nagata's theorem for modules over a valuation ring. -/
private theorem locallyOfFinitePresentation_of_flat_over_valuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f := by
  refine (HasRingHomProperty.iff_of_source_openCover
    (P := @LocallyOfFinitePresentation) (f := f) X.affineCover).2 fun i => ?_
  let g := X.affineCover.f i ≫ f
  have : Flat g := inferInstance
  have : LocallyOfFiniteType g := inferInstance
  let R := Γ(Spec (.of A), ⊤)
  let B := Γ(X.affineCover.X i, ⊤)
  let e : A ≃+* R := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  let _ : IsDomain R := e.isDomain_iff.mp inferInstance
  let _ : PreValuationRing R := ⟨fun a b => by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (e.symm a) (e.symm b)
    · exact ⟨e c, Or.inl (by
        simpa only [map_mul, RingEquiv.apply_symm_apply] using congrArg e hc)⟩
    · exact ⟨e c, Or.inr (by
        simpa only [map_mul, RingEquiv.apply_symm_apply] using congrArg e hc)⟩⟩
  let _ : ValuationRing R := .mk
  let _ : Algebra R B := (g.appTop).hom.toAlgebra
  let _ : Algebra.FiniteType R B := RingHom.finiteType_algebraMap.mp
    (g.finiteType_appLE (isAffineOpen_top (Spec (.of A)))
      (isAffineOpen_top (X.affineCover.X i)) (by simp))
  exact (finitePresentation_of_flat_of_finiteType_of_valuationRing (A := R) (B := B) (M := B)).1
    (g.flat_appLE (isAffineOpen_top (Spec (.of A)))
      (isAffineOpen_top (X.affineCover.X i)) (by simp))

/-- A point of the source over a point of an open `U` of the base lifts to the base change
to `U`. -/
private theorem exists_pullback_fst_eq_of_mem {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    {y : X} (hy : f y ∈ U) : ∃ z, pullback.fst f U.ι z = y := by
  rw [← Set.mem_range, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  exact hy

/-- An open piece of the source on which a flat, finitely presented morphism has constant
relative dimension `d` and which is nonempty has `d ≤ e` whenever the base change of the
morphism to a dense open `U` of the base has relative dimension at most `e`. Flatness makes `f`
open, so the image of the piece meets `U`. -/
private theorem relativeDimension_le_of_dense_open {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (U : S.Opens) (hU : Dense (U : Set S)) (e d : ℕ)
    (hfe : RelativeDimensionLE (pullback.snd f U.ι) e)
    (V : X.Opens) (hVdim : RelativeDimension (V.ι ≫ f) d) (hV : (V : Set X).Nonempty) :
    d ≤ e := by
  have : LocallyOfFiniteType (V.ι ≫ f) := inferInstance
  let _ : UniversallyOpen f := UniversallyOpen.of_flat f
  have himage : (f '' (V : Set X)).Nonempty := by
    obtain ⟨w, hw⟩ := hV
    exact ⟨f w, w, hw, rfl⟩
  obtain ⟨s, ⟨y, hyV, hys⟩, hsU⟩ := hU.inter_open_nonempty _ (f.isOpenMap _ V.2) himage
  have hyU : f y ∈ (U : Set S) := hys ▸ hsU
  obtain ⟨z, hzfst⟩ := exists_pullback_fst_eq_of_mem f U hyU
  have hbound : topologicalKrullDimAt (f.fiber (f ((pullback.fst f U.ι) z)))
      (f.asFiber ((pullback.fst f U.ι) z)) ≤ (e : WithBot ℕ∞) :=
    (topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback f U.ι) z).symm ▸
      (relativeDimensionLEAt_iff _ _ _).mp (hfe.at z)
  have hd : (d : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) :=
    topologicalKrullDimAt_fiber_eq_of_relativeDimension f V d hVdim ((pullback.fst f U.ι) z)
      (by rw [hzfst]; exact hyV) ▸ hbound
  exact_mod_cast hd

/-- The finitely presented case of Stacks 081L. -/
private theorem relativeDimensionLE_of_dense_open_of_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f]
    [LocallyOfFinitePresentation f] (U : S.Opens) (hU : Dense (U : Set S)) (e : ℕ)
    (hfe : RelativeDimensionLE (pullback.snd f U.ι) e) : RelativeDimensionLE f e := by
  obtain ⟨V, hVdense, hVdim⟩ := exists_open_relativeDimension_fiberwise_dense f
  intro x
  set s := f x with hs
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  obtain ⟨Z, hZ, hxZ, hZdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      (S.residueField s) (f.fiber s) (f.fiberToSpecResidueField s) (f.asFiber x)
  obtain ⟨η, hηZ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηgen : η ∈ genericPoints (f.fiber s) := by
    change closure ({η} : Set (f.fiber s)) ∈ irreducibleComponents _
    rw [hηZ]
    exact hZ
  set y : X := (f.fiberHomeo s η).1 with hy
  have hybase : f y = s := (f.fiberHomeo s η).2
  have hyη : y = f.fiberι s η := Scheme.Hom.fiberHomeo_apply f s η
  have hηin : y ∈ ((iSup V : X.Opens) : Set X) := by
    have hmem := scheme_genericPoints_mem_dense_open (f.fiber s)
      ((iSup V : X.Opens).2.preimage (f.fiberι s).continuous) (hVdense s) hηgen
    rw [hyη]
    exact hmem
  obtain ⟨d, hηd⟩ : ∃ d, y ∈ ((V d : X.Opens) : Set X) := Opens.mem_iSup.mp hηin
  have hd := relativeDimension_le_of_dense_open f U hU e d hfe (V d) (hVdim d) ⟨y, hηd⟩
  have hηas : hybase ▸ f.asFiber y = η :=
    (f.fiberι s).isEmbedding.injective
      ((Stacks.Flatness.fiberι_cast_asFiber f y hybase).trans hyη)
  have hdimη : topologicalKrullDimAt (f.fiber s) η =
      topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) :=
    (congrArg (fun w : f.fiber s => topologicalKrullDimAt (f.fiber s) w) hηas).symm.trans
      (topologicalKrullDimAt_fiber_cast f hybase _)
  change topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (e : WithBot ℕ∞)
  rw [hZdim.symm]
  calc
    topologicalKrullDim Z = topologicalKrullDimAt (f.fiber s) η :=
      (topologicalKrullDimAt_eq_topologicalKrullDim_of_closure_eq (S.residueField s)
        (f.fiber s) (f.fiberToSpecResidueField s) hZ hηZ).symm
    _ = topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) := hdimη
    _ = (d : WithBot ℕ∞) :=
      topologicalKrullDimAt_fiber_eq_of_relativeDimension f (V d) d (hVdim d) y hηd
    _ ≤ (e : WithBot ℕ∞) := by exact_mod_cast hd

/-- **Stacks Project, Tag 081L.** A relative-dimension bound for a flat morphism locally of finite
type extends from a dense open of the base when the morphism is locally of finite presentation or
the open is retrocompact. -/
@[stacks 081L]
theorem relativeDimensionLE_of_dense_open {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFiniteType f] (U : S.Opens) (hU : Dense (U : Set S)) (e : ℕ)
    (hfe : RelativeDimensionLE (pullback.snd f U.ι) e)
    (hfin : LocallyOfFinitePresentation f ∨ IsRetrocompact (U : Set S)) :
    RelativeDimensionLE f e := by
  rcases hfin with hfp | hretro
  · let _ : LocallyOfFinitePresentation f := hfp
    exact relativeDimensionLE_of_dense_open_of_locallyOfFinitePresentation f U hU e hfe
  · let _ : QuasiCompact U.ι := quasiCompact_iff_isSpectralMap.2
      (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hretro)
    intro x
    obtain ⟨z, hz⟩ := exists_imageι_eq_of_denseRange U.ι
      (by simpa only [Scheme.Opens.range_ι] using hU) (f x)
    obtain ⟨A, hA, hAd, hAv, K, hK, hAK, hAF, g, h, hcomm, hclosed⟩ :=
      exists_valuationRing_of_image_point U.ι z
    let _ : CommRing A := hA
    let _ : IsDomain A := hAd
    let _ : ValuationRing A := hAv
    let _ : Field K := hK
    let _ : Algebra A K := hAK
    let _ : IsFractionRing A K := hAF
    let T := Spec (.of A)
    let p : T ⟶ S := h ≫ U.ι.imageι
    let j : Spec (.of K) ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap A K))
    have hclosedS : p (closedPoint A) = f x := by
      change U.ι.imageι (h (closedPoint A)) = f x
      rw [hclosed, hz]
    have hcommS : g ≫ U.ι = j ≫ p := by
      calc
        g ≫ U.ι = (g ≫ U.ι.toImage) ≫ U.ι.imageι := by
          rw [Category.assoc, Scheme.Hom.toImage_imageι]
        _ = (j ≫ h) ≫ U.ι.imageι := by rw [hcomm]
        _ = j ≫ p := by simp [p, Category.assoc]
    have hgen : j (genericPoint (Spec (.of K))) = genericPoint T := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).mp
        (IsFractionRing.injective A K))
    set W : T.Opens := p ⁻¹ᵁ U with hW
    have hWgen : genericPoint T ∈ W := by
      have hpoint : U.ι (g (genericPoint (Spec (.of K)))) =
          p (j (genericPoint (Spec (.of K)))) :=
        congrArg (fun k : Spec (.of K) ⟶ S => k (genericPoint (Spec (.of K)))) hcommS
      change p (genericPoint T) ∈ (U : Set S)
      rw [← hgen, hpoint.symm]
      exact (g (genericPoint (Spec (.of K)))).property
    have : IrreducibleSpace T := inferInstance
    have hgenericDense : Dense ({genericPoint T} : Set T) := fun t =>
      specializes_iff_mem_closure.mp (genericPoint_specializes t)
    have hWdense : Dense (W : Set T) :=
      hgenericDense.mono (Set.singleton_subset_iff.mpr hWgen)
    set fT := pullback.snd f p with hfT
    have : Flat fT := inferInstance
    have : LocallyOfFiniteType fT := inferInstance
    have : LocallyOfFinitePresentation fT :=
      locallyOfFinitePresentation_of_flat_over_valuationRing fT
    have hfeT : RelativeDimensionLE (pullback.snd fT W.ι) e := by
      intro q
      set y := pullback.fst fT W.ι q with hyq
      set w := pullback.snd fT W.ι q with hwq
      set yX := pullback.fst f p y with hyX
      have hout : fT y = W.ι w := by
        have hc := congrArg (fun k : pullback fT W.ι ⟶ T => k q)
          (pullback.condition (f := fT) (g := W.ι))
        simpa [hyq, hwq, Scheme.Hom.comp_apply] using hc
      have hinner : f yX = p (fT y) := by
        have hc := congrArg (fun k : pullback f p ⟶ S => k y)
          (pullback.condition (f := f) (g := p))
        simpa [hyX, Scheme.Hom.comp_apply] using hc
      obtain ⟨xU, hlift⟩ := exists_pullback_fst_eq_of_mem f U (y := yX)
        (by rw [hinner, hout]; exact w.property)
      have hdimU := topologicalKrullDimAt_fiber_eq_of_isPullback
        (IsPullback.of_hasPullback f U.ι) xU
      rw [hlift] at hdimU
      refine (relativeDimensionLEAt_iff _ _ _).2 ?_
      calc
        topologicalKrullDimAt ((pullback.snd fT W.ι).fiber ((pullback.snd fT W.ι) q))
            ((pullback.snd fT W.ι).asFiber q)
          = topologicalKrullDimAt (fT.fiber (fT y)) (fT.asFiber y) :=
            topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback fT W.ι) q
        _ = topologicalKrullDimAt (f.fiber (f yX)) (f.asFiber yX) :=
            topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback f p) y
        _ = topologicalKrullDimAt ((pullback.snd f U.ι).fiber ((pullback.snd f U.ι) xU))
            ((pullback.snd f U.ι).asFiber xU) := hdimU.symm
        _ ≤ (e : WithBot ℕ∞) := (relativeDimensionLEAt_iff _ _ _).mp (hfe.at xU)
    have hresult := relativeDimensionLE_of_dense_open_of_locallyOfFinitePresentation
      fT W hWdense e hfeT
    obtain ⟨q, hqfst, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := p) x (closedPoint A) hclosedS.symm
    change topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (e : WithBot ℕ∞)
    calc
      _ = topologicalKrullDimAt (f.fiber (f (pullback.fst f p q)))
          (f.asFiber (pullback.fst f p q)) := by rw [hqfst]
      _ = topologicalKrullDimAt (fT.fiber (fT q)) (fT.asFiber q) :=
        (topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback f p) q).symm
      _ ≤ (e : WithBot ℕ∞) := (relativeDimensionLEAt_iff _ _ _).mp (hresult.at q)

end AlgebraicGeometry

end
