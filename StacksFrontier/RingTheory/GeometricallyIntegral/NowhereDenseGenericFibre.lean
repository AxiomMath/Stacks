module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourcePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus

/-!
# Nowhere dense generic fibre

**Stacks 054X.** Let `f : X ⟶ Y` be a finite type morphism of schemes with `Y` irreducible with
generic point `η`, and let `Z ⊆ X` be closed. If `Z_η` is nowhere dense in `X_η`, then `Z_y` is
nowhere dense in `X_y` for every `y` in some nonempty open `V ⊆ Y`.

This is the statement that lets the first proof of Stacks 0559 shrink the base so that a common
affine open of two schemes over `Y` is fibrewise dense: apply it to the complement of the open.

## The argument

The source's proof runs in two steps.

*Reduction to a reduced base.* Replace `Y` by its reduction `Y'` and `X` by `Y' ×_Y X`. The
morphism `Y' ⟶ Y` is a universal homeomorphism (Stacks 054M), hence so is its base change
`Y' ×_Y X ⟶ X`, and nowhere density in fibres is a purely topological condition invariant under a
homeomorphism of the whole situation
(`AlgebraicGeometry.isNowhereDense_fiberι_preimage_iff_of_isHomeomorph`). So it suffices to treat
a reduced base.

*The dimension count.* Over a reduced base, generic flatness (Stacks 052B, in the form
`AlgebraicGeometry.exists_dense_open_flat_finitePresentation_structureSheaf`) gives dense opens
`U` and `V` of `Y` over which `X` and the reduced closed subscheme `T` cut out by `Z` are
respectively flat and of finite presentation. The claim is that `W = U ∩ V` works; it contains
`η` because `η` lies in every dense open. Suppose `Z_y` had nonempty interior for some `y ∈ W`.
Then `Z_y` contains a generic point `ξ` of an irreducible component of `X_y` (Stacks 0A21 is not
needed for this: it is `exists_mem_genericPoints_of_not_isNowhereDense`, since the fibre is a
Noetherian sober space).
Flatness of `T ⟶ V` generalizes `ξ`, viewed in `T`, to a point `ξ'` of `T` over `η`. Stacks 054U
makes the local dimension of the fibre constant along that specialization, on `X` and on `T`
separately, so

  `dim_{ξ'}(Z_η) = dim_{ξ}(Z_y) = dim_{ξ}(X_y) = dim_{ξ'}(X_η)`,

the middle equality because `ξ` is generic in a component of `X_y` and lies in `Z_y`, so the
closed immersion `T_y ⟶ X_y` is generic on both sides at it. Hence the component of `Z_η` through
`ξ'` has the local dimension of `X_η` at `ξ'`; since both are finite, the inclusion of that
component into the component of `X_η` it sits in cannot be strict, so the component is a
component of `X_η`, and its generic point has a neighbourhood inside `Z_η`. That contradicts
nowhere density of `Z_η`.

## Main results

* `AlgebraicGeometry.exists_open_isNowhereDense_fiber` is Stacks 054X.
* `AlgebraicGeometry.exists_open_isNowhereDense_fiber_of_isReduced` is the case of a reduced base,
  which carries the dimension count.

## Implementation notes

A finite type morphism is `LocallyOfFiniteType` together with `QuasiCompact`. The fibre of a
subset `Z ⊆ X` over `y` is its preimage under `AlgebraicGeometry.Scheme.Hom.fiberι`, and nowhere
density is Mathlib's `IsNowhereDense`, so "nowhere dense in `X_y`" is
`IsNowhereDense ((f.fiberι y) ⁻¹' Z)`.

The closed subset `Z` is given the reduced induced structure
`(Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme`, whose support is `Z` and which is a
closed subscheme of `X`; what the proof uses of it is only that its underlying set is `Z` and
that it is a scheme, so that generic flatness applies to it.

`AlgebraicGeometry.Scheme.Hom.asFiberAt` names the point of `f.fiber y` determined by a point of
`X` lying over `y`, for an arbitrary proof of `f x = y` rather than only `rfl`. Without it the
dimension equalities are between fibres over syntactically different points and no `rw` applies;
with it the transport is by `cases` on the equality.

## References

* [Stacks Project, Tag 054X](https://stacks.math.columbia.edu/tag/054X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The point of a fibre determined by a point of the source -/

/-- `asFiberAt` depends only on the point of the source, not on the proof. -/
lemma Scheme.Hom.fiberPt_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X} (hxx : x = x') (y : Y)
    (h : f x = y) (h' : f x' = y) : f.asFiberAt x y h = f.asFiberAt x' y h' := by
  cases hxx
  simp [Scheme.Hom.asFiberAt]

/-- `asFiberAt` is a section of the fibre inclusion. -/
lemma Scheme.Hom.fiberι_fiberPt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    f.fiberι y (f.asFiberAt x y h) = x := by
  cases h
  exact f.fiberι_asFiber x

/-- Genericity of `f.asFiber x` in the fibre over `f x` transports to `asFiberAt`. -/
lemma Scheme.Hom.mem_genericPoints_fiberPt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) (hx : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    f.asFiberAt x y h ∈ genericPoints (f.fiber y) := by
  cases h
  exact hx

/-- The local dimension of a fibre at `asFiberAt` is the local dimension at `asFiber`. -/
lemma Scheme.Hom.topologicalKrullDimAt_fiberPt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber y) (f.asFiberAt x y h) := by
  cases h
  rfl

/-- The comparison morphism of fibres sends `asFiberAt` of the source to `asFiberAt` of the
target. -/
lemma Scheme.Hom.fiberMap_fiberPt {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (t : T) (s : S)
    (h : (i ≫ f) t = s) :
    f.fiberMap i s (Scheme.Hom.asFiberAt (i ≫ f) t s h) =
      f.asFiberAt (i t) s ((Scheme.Hom.comp_apply i f t).symm.trans h) := by
  apply (f.fiberι s).isEmbedding.injective
  calc
    f.fiberι s (f.fiberMap i s (Scheme.Hom.asFiberAt (i ≫ f) t s h)) =
        i ((i ≫ f).fiberι s (Scheme.Hom.asFiberAt (i ≫ f) t s h)) := f.fiberι_fiberMap i s _
    _ = i t := congrArg i ((i ≫ f).fiberι_fiberPt t s h)
    _ = f.fiberι s (f.asFiberAt (i t) s ((Scheme.Hom.comp_apply i f t).symm.trans h)) :=
      (f.fiberι_fiberPt (i t) s ((Scheme.Hom.comp_apply i f t).symm.trans h)).symm

/-- `fiberMap` sends `asFiberAt` of a point of `T` to `asFiberAt` of its image `x`. -/
private theorem fiberMap_asFiberAt_of_eq {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (t : T)
    (x : X) (s : S) (hx : i t = x) (h : (i ≫ f) t = s) (h' : f x = s) :
    f.fiberMap i s ((i ≫ f).asFiberAt t s h) = f.asFiberAt x s h' := by
  subst hx
  exact Scheme.Hom.fiberMap_fiberPt i f t s h

/-- Fibres of a quasi-compact morphism locally of finite type are Noetherian spaces. -/
private theorem noetherianSpace_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] (y : Y) : NoetherianSpace (f.fiber y) :=
  have := isLocallyNoetherian_fiber_of_locallyOfFiniteType f y
  have : IsNoetherian (f.fiber y) := {}
  inferInstance

/-! ### The dimension count over a reduced base -/

/-- **Stacks Project, Tag 054X over a reduced base.** The case of Stacks 054X in which the
irreducible base is moreover reduced; this is where the dimension count happens. The general case
reduces to it along the universal homeomorphism given by the reduction of the base.

Irreducibility of `Y` is not assumed separately: the hypothesis that `η` is a generic point of
the whole of `Y` already supplies everything the argument uses of it, so this is stated without
an `IrreducibleSpace` instance and is correspondingly more general than
`AlgebraicGeometry.exists_open_isNowhereDense_fiber`. -/
theorem exists_open_isNowhereDense_fiber_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsReduced Y] [LocallyOfFiniteType f] [QuasiCompact f] (Z : Set X)
    (hZ : IsClosed Z) (η : Y) (hη : IsGenericPoint η Set.univ)
    (hηZ : IsNowhereDense ((f.fiberι η) ⁻¹' Z)) :
    ∃ W : Set Y, IsOpen W ∧ W.Nonempty ∧ ∀ y ∈ W, IsNowhereDense ((f.fiberι y) ⁻¹' Z) := by
  obtain ⟨U, V, hU, hV, hflatF, hfpF, hflatG, hfpG⟩ :=
    exists_dense_opens_flat_source_and_closed f Z hZ
  have hηU : η ∈ U := hη.mem_of_isOpen_of_dense U.2 hU
  have hηV : η ∈ V := hη.mem_of_isOpen_of_dense V.2 hV
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩
  let i : I.subscheme ⟶ X := I.subschemeι
  let g : I.subscheme ⟶ Y := i ≫ f
  have : LocallyOfFiniteType g := inferInstance
  have : QuasiCompact g := inferInstance
  let UX : X.Opens := f ⁻¹ᵁ U
  let jX : UX.toScheme ⟶ X := UX.ι
  let fU : UX.toScheme ⟶ Y := jX ≫ f
  have hfacF : fU = f.resLE U UX le_rfl ≫ U.ι := by
    dsimp [fU, jX]
    exact (Scheme.Hom.resLE_comp_ι f le_rfl).symm
  let TV : I.subscheme.Opens := g ⁻¹ᵁ V
  let jT : TV.toScheme ⟶ I.subscheme := TV.ι
  let gV : TV.toScheme ⟶ Y := jT ≫ g
  have hfacG : gV = g.resLE V TV le_rfl ≫ V.ι := by
    dsimp [gV, jT]
    exact (Scheme.Hom.resLE_comp_ι g le_rfl).symm
  have : Flat (f.resLE U UX le_rfl) := hflatF
  have : FinitePresentation (f.resLE U UX le_rfl) := hfpF
  have : Flat (g.resLE V TV le_rfl) := hflatG
  have : FinitePresentation (g.resLE V TV le_rfl) := hfpG
  have : LocallyOfFinitePresentation (f.resLE U UX le_rfl) := hfpF.locallyOfFinitePresentation
  have : LocallyOfFinitePresentation (g.resLE V TV le_rfl) := hfpG.locallyOfFinitePresentation
  have : Flat fU := by rw [hfacF]; infer_instance
  have : LocallyOfFinitePresentation fU := by rw [hfacF]; infer_instance
  have : Flat gV := by rw [hfacG]; infer_instance
  have : LocallyOfFinitePresentation gV := by rw [hfacG]; infer_instance
  refine ⟨(U : Set Y) ∩ (V : Set Y), U.2.inter V.2, ⟨η, Set.mem_inter hηU hηV⟩, ?_⟩
  intro y hy
  obtain ⟨hyU, hyV⟩ := hy
  let A : Set (f.fiber y) := (f.fiberι y) ⁻¹' Z
  have hAclosed : IsClosed A := hZ.preimage (f.fiberι y).continuous
  by_contra hnd
  have hnotA : ¬ IsNowhereDense A := by simpa [A] using hnd
  have := noetherianSpace_fiber f y
  have : QuasiSober (f.fiber y) := inferInstance
  obtain ⟨p, hpA, hpgen⟩ := exists_mem_genericPoints_of_not_isNowhereDense hAclosed hnotA
  rcases hpt : f.fiberHomeo y p with ⟨x, hxy⟩
  have hfy : f x = y := by simpa using hxy
  have hxEq : x = f.fiberι y p := by
    have hval := congrArg (fun q : f ⁻¹' {y} => (q : X)) hpt
    calc
      x = (f.fiberHomeo y p : f ⁻¹' {y}) := hval.symm
      _ = f.fiberι y p := Scheme.Hom.fiberHomeo_apply f y p
  cases hfy
  let y : Y := f x
  have hpAsFiber : f.asFiber x = p := by
    apply (f.fiberι (f x)).isEmbedding.injective
    rw [Scheme.Hom.fiberι_asFiber]
    simp [hxEq]
  have hpgenX : f.asFiber x ∈ genericPoints (f.fiber y) := by simpa [hpAsFiber] using hpgen
  have hxU : x ∈ UX := hyU
  let xU : (↑UX) := ⟨x, hxU⟩
  have hxUval : jX xU = x := rfl
  have hbaseX : fU xU = y := by
    show (jX ≫ f) xU = f x
    rw [Scheme.Hom.comp_apply, hxUval]
  have hbasePX : f x = fU xU := by simpa [y] using hbaseX.symm
  have hmapX : f.fiberMap jX (fU xU) (fU.asFiber xU) = f.asFiberAt x (fU xU) hbasePX := by
    exact fiberMap_asFiberAt_of_eq jX f xU x (fU xU) rfl rfl hbasePX
  have hgenU : fU.asFiber xU ∈ genericPoints (fU.fiber (fU xU)) := by
    refine genericPoints_preimage_of_isOpenImmersion (f.fiberMap jX (fU xU)) ?_
    rw [hmapX]
    exact f.mem_genericPoints_fiberPt x (fU xU) hbasePX hpgenX
  obtain ⟨t, htZ⟩ : ∃ t : I.subscheme, i t = x := by
    have hxSupport : x ∈ (I.support : Set X) := by
      have hsupport : (I.support : Set X) = Z :=
        Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨Z, hZ⟩
      rw [hsupport]
      simpa [A, hxEq] using hpA
    have hxRange : x ∈ Set.range i := by rw [I.range_subschemeι]; exact hxSupport
    exact hxRange
  have hgt : g t = f x := by simp [g, i, htZ]
  have hxfBase : f x = g t := hgt.symm
  have hmapT : f.fiberMap i (g t) (g.asFiber t) = f.asFiberAt x (g t) hxfBase := by
    exact fiberMap_asFiberAt_of_eq i f t x (g t) htZ rfl hxfBase
  have hgenT : g.asFiber t ∈ genericPoints (g.fiber (g t)) := by
    refine genericPoints_preimage_of_isClosedImmersion (f.fiberMap i (g t)) ?_
    rw [hmapT]
    exact f.mem_genericPoints_fiberPt x (g t) hxfBase hpgenX
  have htV : t ∈ TV := by
    show g t ∈ V
    rw [hgt]
    exact hyV
  let tV : (↑TV) := ⟨t, htV⟩
  have hbaseT : gV tV = y := by
    show (jT ≫ g) tV = f x
    rw [Scheme.Hom.comp_apply]
    exact hgt
  have htVval : jT tV = t := rfl
  have hgtV : g t = gV tV := hgt.trans hbaseT.symm
  have hmapV : g.fiberMap jT (gV tV) (gV.asFiber tV) = g.asFiberAt t (gV tV) hgtV := by
    exact fiberMap_asFiberAt_of_eq jT g tV t (gV tV) rfl rfl hgtV
  have hgenV : gV.asFiber tV ∈ genericPoints (gV.fiber (gV tV)) := by
    refine genericPoints_preimage_of_isOpenImmersion (g.fiberMap jT (gV tV)) ?_
    rw [hmapV]
    exact g.mem_genericPoints_fiberPt t (gV tV) hgtV hgenT
  have hηy : η ⤳ f x := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [hη.def]
    exact Set.mem_univ (f x)
  obtain ⟨tηV, htSpec, htBase⟩ :=
    (Flat.generalizingMap gV) (show η ⤳ gV tV from by simpa [hbaseT] using hηy)
  let tη : I.subscheme := jT tηV
  have htηbase : g tη = η := by simpa [gV, jT, tη] using htBase
  have htSpecializes : tη ⤳ t := htSpec.map jT.continuous
  let xη : X := i tη
  have hxηbase : f xη = η := by simpa [g, i, xη, htηbase] using htηbase
  have hxηU : xη ∈ UX := by
    show f xη ∈ U
    rw [hxηbase]
    exact hηU
  let xηU : (↑UX) := ⟨xη, hxηU⟩
  have hxSpecializes : xηU ⤳ xU := by
    refine specializes_iff_mem_closure.mpr ?_
    have hxcl : x ∈ closure ({xη} : Set X) := by
      simpa [xη, tη, htZ] using (specializes_iff_mem_closure.mp (htSpecializes.map i.continuous))
    have hxpre : xU ∈ UX.ι ⁻¹' closure ({xη} : Set X) := hxcl
    rw [UX.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      UX.ι.continuous] at hxpre
    have hpreimage : UX.ι ⁻¹' ({xη} : Set X) = ({xηU} : Set (↑UX)) := by
      ext z
      exact ⟨fun hz => Subtype.ext hz, fun hz => congrArg Subtype.val hz⟩
    simpa only [hpreimage] using hxpre
  obtain ⟨dF, hdF⟩ :=
    exists_nat_topologicalKrullDimAt_fiber_of_mem_genericPoints fU hgenU
  obtain ⟨dG, hdG⟩ :=
    exists_nat_topologicalKrullDimAt_fiber_of_mem_genericPoints gV hgenV
  have hspecDimF :=
    topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints fU hxSpecializes hgenU
  have hspecDimG :=
    topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints gV htSpec hgenV
  have hopenDimFη := fiberDimensionAt_comp_openImmersion UX.ι f xηU
  have hopenDimFy := fiberDimensionAt_comp_openImmersion UX.ι f xU
  have hopenDimGη := fiberDimensionAt_comp_openImmersion TV.ι g tηV
  have hopenDimGy := fiberDimensionAt_comp_openImmersion TV.ι g tV
  have hdimFη : topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) =
      topologicalKrullDimAt (f.fiber y) (f.asFiber x) := by
    have hOpenFη : topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) =
        topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xηU))
          ((UX.ι ≫ f).asFiber xηU) := by
      convert hopenDimFη.symm using 1
      rfl
    have hOpenFy : topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xU))
          ((UX.ι ≫ f).asFiber xU) = topologicalKrullDimAt (f.fiber y) (f.asFiber x) := by
      convert hopenDimFy using 1
      rfl
    have hspecDimF' : topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xηU))
          ((UX.ι ≫ f).asFiber xηU) =
        topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xU))
          ((UX.ι ≫ f).asFiber xU) := by
      simpa [fU, jX] using hspecDimF
    exact hOpenFη.trans (hspecDimF'.trans hOpenFy)
  have hdimGη : topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) =
      topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) := by
    have hOpenGη : topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) =
        topologicalKrullDimAt ((TV.ι ≫ g).fiber ((TV.ι ≫ g) tηV))
          ((TV.ι ≫ g).asFiber tηV) := by
      simpa [jT, tη] using hopenDimGη.symm
    have hspecDimG' : topologicalKrullDimAt ((TV.ι ≫ g).fiber ((TV.ι ≫ g) tηV))
          ((TV.ι ≫ g).asFiber tηV) =
        topologicalKrullDimAt ((TV.ι ≫ g).fiber ((TV.ι ≫ g) tV))
          ((TV.ι ≫ g).asFiber tV) := by
      simpa [gV, jT] using hspecDimG
    exact hOpenGη.trans (hspecDimG'.trans hopenDimGy)
  have hgtTV : g (jT tV) = y := by rw [htVval]; exact hgt
  have hgenTV : g.asFiberAt (jT tV) y hgtTV ∈ genericPoints (g.fiber y) := by
    refine g.mem_genericPoints_fiberPt (jT tV) y hgtTV ?_
    have hb : g t = g (jT tV) := congrArg g htVval.symm
    have hc := g.mem_genericPoints_fiberPt t (g (jT tV)) hb hgenT
    have hp' : g.asFiberAt t (g (jT tV)) hb = g.asFiber (jT tV) := by
      simpa [Scheme.Hom.asFiberAt] using g.fiberPt_congr htVval.symm (g (jT tV)) hb rfl
    rw [← hp']
    exact hc
  have hxfy : f x = y := rfl
  have hpgenXY : f.asFiberAt x y hxfy ∈ genericPoints (f.fiber y) :=
    f.mem_genericPoints_fiberPt x y hxfy hpgenX
  have hix : i (jT tV) = x := by rw [htVval]; exact htZ
  have hmapY : f.fiberMap i y (g.asFiberAt (jT tV) y hgtTV) = f.asFiberAt x y hxfy := by
    exact fiberMap_asFiberAt_of_eq i f (jT tV) x y hix (by rw [Scheme.Hom.comp_apply, hix]) hxfy
  have hdimAtY : topologicalKrullDimAt (g.fiber y) (g.asFiberAt (jT tV) y hgtTV) =
      topologicalKrullDimAt (f.fiber y) (f.asFiberAt x y hxfy) := by
    have hraw := topologicalKrullDimAt_eq_of_isClosedImmersion_genericPoints (f.fiberMap i y)
      (Y.residueField y) (g.fiberToSpecResidueField y) (f.fiberToSpecResidueField y)
      hgenTV (by rw [hmapY]; exact hpgenXY)
    simpa [g, hmapY] using hraw
  have hdimη : topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) =
      topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := by
    calc
      _ = topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) := hdimGη
      _ = topologicalKrullDimAt (g.fiber y) (g.asFiberAt (jT tV) y hgtTV) :=
        g.topologicalKrullDimAt_fiberPt (jT tV) y hgtTV
      _ = topologicalKrullDimAt (f.fiber y) (f.asFiberAt x y hxfy) := hdimAtY
      _ = topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) :=
        (f.topologicalKrullDimAt_fiberPt x y hxfy).symm
      _ = topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := hdimFη.symm
  have hdGspecial : topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) =
      (dG : WithBot ℕ∞) := hopenDimGy.symm.trans hdG
  have hfiniteGη : topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) ≠ ⊤ := by
    rw [hdimGη, hdGspecial]
    exact ne_of_lt (WithBot.coe_lt_coe.mpr (by simp))
  obtain ⟨B, hB, htηB, hBdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      (Y.residueField (f xη)) (g.fiber (f xη)) (g.fiberToSpecResidueField (f xη))
      (g.asFiberAt tη (f xη) (htηbase.trans hxηbase.symm))
  let φ : g.fiber (f xη) ⟶ f.fiber (f xη) := f.fiberMap i (f xη)
  let D : Set (f.fiber (f xη)) := φ '' B
  have hBclosed : IsClosed B := isClosed_of_mem_irreducibleComponents B hB
  have hDclosed : IsClosed D := φ.isClosedEmbedding.isClosedMap B hBclosed
  have hDirr : IsIrreducible D := hB.1.image φ φ.continuous.continuousOn
  have hηbaseG : g tη = f xη := htηbase.trans hxηbase.symm
  have hpoint : φ (g.asFiberAt tη (f xη) hηbaseG) = f.asFiber xη := by
    exact fiberMap_asFiberAt_of_eq i f tη xη (f xη) rfl hηbaseG rfl
  have hDdim : topologicalKrullDim D =
      topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := by
    calc
      topologicalKrullDim D = topologicalKrullDim B :=
        ((φ.isEmbedding.homeomorphImage B).isHomeomorph.topologicalKrullDim_eq _).symm
      _ = topologicalKrullDimAt (g.fiber (f xη)) (g.asFiberAt tη (f xη) hηbaseG) := hBdim
      _ = topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) :=
        (g.topologicalKrullDimAt_fiberPt tη (f xη) hηbaseG).symm
      _ = topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := hdimη
  have hxηD : f.asFiber xη ∈ D := ⟨g.asFiberAt tη (f xη) hηbaseG, htηB, hpoint⟩
  obtain ⟨C, hC, hDC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible D hDirr
  have hxηC : f.asFiber xη ∈ C := hDC hxηD
  have := noetherianSpace_fiber f (f xη)
  have hCdimle : topologicalKrullDim C ≤
      topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents (Y.residueField (f xη))
      (f.fiber (f xη)) (f.fiberToSpecResidueField (f xη)) (f.asFiber xη)]
    exact le_iSup_of_le C (le_iSup_of_le ⟨hC, hxηC⟩ le_rfl)
  let D' : IrreducibleCloseds (f.fiber (f xη)) := ⟨D, hDirr, hDclosed⟩
  let C' : IrreducibleCloseds (f.fiber (f xη)) :=
    ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have hDfinite : topologicalKrullDim D ≠ ⊤ := by
    rw [hDdim, ← hdimη]
    exact hfiniteGη
  have hsetEq : D = C := by
    refine congrArg IrreducibleCloseds.carrier (by_contra fun hne => ?_ : D' = C')
    have hstrict : topologicalKrullDim D < topologicalKrullDim C := by
      simpa [D', C'] using topologicalKrullDim_coe_lt_coe_of_lt D' C'
        (lt_of_le_of_ne (show D' ≤ C' from hDC) hne) (by simpa [D'] using hDfinite)
    exact (not_lt_of_ge hCdimle) (hDdim ▸ hstrict)
  have hDsubsetZ : D ⊆ (f.fiberι (f xη)) ⁻¹' Z := by
    rintro z ⟨z', hz', rfl⟩
    show f.fiberι (f xη) (φ z') ∈ Z
    rw [show f.fiberι (f xη) (φ z') = i ((i ≫ f).fiberι (f xη) z') from
      f.fiberι_fiberMap i (f xη) z']
    have hrange : i ((i ≫ f).fiberι (f xη) z') ∈ Set.range i := ⟨_, rfl⟩
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hrange
    exact hrange
  have hCsubsetZ : C ⊆ (f.fiberι (f xη)) ⁻¹' Z := by simpa [hsetEq] using hDsubsetZ
  let c : genericPoints (f.fiber (f xη)) := genericPoints.ofComponent ⟨C, hC⟩
  obtain ⟨O, hO, hOne, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({c.1} : Set (f.fiber (f xη)))) c.2
  have hc : closure ({c.1} : Set (f.fiber (f xη))) = C :=
    (genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩).def
  have hOA : O ⊆ (f.fiberι (f xη)) ⁻¹' Z := by
    rw [← hc] at hCsubsetZ
    exact hOC.trans hCsubsetZ
  obtain ⟨z, hz⟩ := hOne
  refine (Set.nonempty_iff_ne_empty.mp ⟨z, (hO.subset_interior_iff.mpr hOA) hz⟩) ?_
  have hηZ' := isNowhereDense_fiberι_preimage_congr f η (f xη) hxηbase.symm Z hηZ
  rw [IsNowhereDense, (hZ.preimage (f.fiberι (f xη)).continuous).closure_eq] at hηZ'
  exact hηZ'

/-! ### Stacks 054X -/

/-- **Stacks Project, Tag 054X.** A closed subset that is nowhere dense in the generic fibre of a
finite type morphism remains nowhere dense in all fibres over a nonempty open subset of the
irreducible base.

The base is replaced by its reduction, which is a universal homeomorphism onto it (Stacks 054M),
so the base change of `f` is a homeomorphism onto `X`; nowhere density in fibres is invariant
under that, and the reduced base is handled by
`AlgebraicGeometry.exists_open_isNowhereDense_fiber_of_isReduced`. -/
@[stacks 054X]
theorem exists_open_isNowhereDense_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (Z : Set X) (hZ : IsClosed Z) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hηZ : IsNowhereDense ((f.fiberι η) ⁻¹' Z)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, IsNowhereDense ((f.fiberι y) ⁻¹' Z) := by
  let r : Y.nilradical.subscheme ⟶ Y := Y.nilradical.subschemeι
  let P : Scheme.{u} := pullback f r
  let a : P ⟶ X := pullback.fst f r
  let g : P ⟶ Y.nilradical.subscheme := pullback.snd f r
  have hr : UniversalHomeomorphism r := inferInstance
  have hbase : UniversalHomeomorphism a :=
    ⟨(MorphismProperty.universally_isStableUnderBaseChange
      (topologically @IsHomeomorph)).of_isPullback
        (IsPullback.of_hasPullback f r).flip hr.universally_isHomeomorph⟩
  have ha : IsHomeomorph a := hbase.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hb : IsHomeomorph r := hr.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  let eY : Y.nilradical.subscheme ≃ₜ Y := hb.homeomorph r
  have hη' : IsGenericPoint (eY.symm η) Set.univ := by
    show closure ({eY.symm η} : Set Y.nilradical.subscheme) = Set.univ
    calc
      closure ({eY.symm η} : Set Y.nilradical.subscheme) = eY.symm '' closure ({η} : Set Y) := by
        rw [eY.symm.image_closure]
        simp
      _ = Set.univ := by rw [hη.def]; simp
  have : IsReduced Y.nilradical.subscheme := isReduced_nilradical_subscheme Y
  have : IrreducibleSpace Y.nilradical.subscheme := eY.irreducibleSpace_iff.mpr inferInstance
  have : LocallyOfFiniteType g := by
    show LocallyOfFiniteType (pullback.snd f r)
    infer_instance
  have : QuasiCompact g := by
    show QuasiCompact (pullback.snd f r)
    infer_instance
  have hcomm (z : P) : f (a z) = r (g z) := congrArg (fun k : P ⟶ Y => k z) pullback.condition
  have hηZ' : IsNowhereDense ((g.fiberι (eY.symm η)) ⁻¹' (a ⁻¹' Z)) := by
    refine (isNowhereDense_fiberι_preimage_iff_of_isHomeomorph f g a r ha hb hcomm (eY.symm η)
      (a ⁻¹' Z) Z (fun z => Iff.rfl)).mpr ?_
    exact (show r (eY.symm η) = η from eY.apply_symm_apply η).symm ▸ hηZ
  obtain ⟨V', hV', hV'ne, hV'fib⟩ :=
    exists_open_isNowhereDense_fiber_of_isReduced g (a ⁻¹' Z) (hZ.preimage ha.continuous)
      (eY.symm η) hη' hηZ'
  refine ⟨eY '' V', eY.isOpenMap _ hV', hV'ne.image _, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact (isNowhereDense_fiberι_preimage_iff_of_isHomeomorph f g a r ha hb hcomm y'
    (a ⁻¹' Z) Z fun _ => Iff.rfl).mp (hV'fib y' hy')

/-! ### Guards: the statement is not vacuous, and the hypothesis is not removable

The conclusion of Stacks 054X asserts nowhere density of a fibre, and nowhere density of a
*junk* fibre would be free, so the two extremes of the locus `{y | Z_y is nowhere dense in X_y}`
are recorded here. For `Z = ∅` the locus is everything, for `Z = X` and `f` surjective it is
empty — so the locus is not constantly true, the conclusion is not free, and the hypothesis
`hηZ` cannot be dropped.
-/

/-- One extreme: the empty closed subset is nowhere dense in every fibre. -/
theorem isNowhereDense_fiberι_preimage_empty {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    IsNowhereDense ((f.fiberι y) ⁻¹' (∅ : Set X)) := by
  simp [IsNowhereDense]

/-- The other extreme: the whole source is **not** nowhere dense in any nonempty fibre. The
fibre over `f x` is nonempty, being inhabited by `f.asFiber x`. -/
theorem not_isNowhereDense_fiberι_preimage_univ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ¬ IsNowhereDense ((f.fiberι (f x)) ⁻¹' (Set.univ : Set X)) := by
  rw [Set.preimage_univ, IsNowhereDense, closure_univ, interior_univ]
  exact fun h => (h ▸ Set.mem_univ (f.asFiber x) : (f.asFiber x) ∈ (∅ : Set (f.fiber (f x))))

/-- **The hypothesis of Stacks 054X is not removable.** For `Z = X` and `f` surjective onto a
nonempty base the conclusion is false: every fibre over a point of the base is nonempty, so no
nonempty open of the base has nowhere dense fibres. Hence `hηZ` is doing work, and
`AlgebraicGeometry.exists_open_isNowhereDense_fiber` is not an instance of a statement true for
every closed subset. -/
theorem not_exists_open_isNowhereDense_fiber_univ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] :
    ¬ ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, IsNowhereDense ((f.fiberι y) ⁻¹' (Set.univ : Set X)) := by
  rintro ⟨V, -, ⟨y, hy⟩, hV⟩
  obtain ⟨x, rfl⟩ := (surjective_iff f).mp inferInstance y
  exact not_isNowhereDense_fiberι_preimage_univ f x (hV _ hy)

/-! ### The form Stacks 0559 consumes -/

/-- For an open subset, nowhere density of the complement in a fibre is density in that fibre. -/
theorem dense_fiberι_preimage_iff_isNowhereDense_compl {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    {U : Set X} (hU : IsOpen U) :
    Dense ((f.fiberι y) ⁻¹' U) ↔ IsNowhereDense ((f.fiberι y) ⁻¹' Uᶜ) := by
  rw [Set.preimage_compl, IsNowhereDense,
    (hU.preimage (f.fiberι y).continuous).isClosed_compl.closure_eq, interior_compl,
    Set.compl_empty_iff, dense_iff_closure_eq]

/-- **Stacks 054X in the form the proofs of Stacks 0559 use it.** An open subscheme of the
source whose generic fibre is dense in the generic fibre has dense fibres over a nonempty open of
the base. Applied to a common affine open of two schemes over `Y`, this is the step that lets
0559 shrink `Y` until the open is fibrewise dense.

This declaration deliberately carries no tag attribute: it is a restatement of the tagged
theorem through `AlgebraicGeometry.dense_fiberι_preimage_iff_isNowhereDense_compl`, so the
covering set of tag 054X is the tagged theorem alone and a second placement would over-claim. -/
theorem exists_open_dense_fiber_of_isOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (U : Set X) (hU : IsOpen U) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hηU : Dense ((f.fiberι η) ⁻¹' U)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧ ∀ y ∈ V, Dense ((f.fiberι y) ⁻¹' U) := by
  obtain ⟨V, hVopen, hVne, hVfib⟩ := exists_open_isNowhereDense_fiber f Uᶜ hU.isClosed_compl η hη
    ((dense_fiberι_preimage_iff_isNowhereDense_compl f η hU).mp hηU)
  exact ⟨V, hVopen, hVne,
    fun y hy => (dense_fiberι_preimage_iff_isNowhereDense_compl f y hU).mpr (hVfib y hy)⟩

end AlgebraicGeometry

end
