module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseFibreAux
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourcePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseGenericFibre

/-!
# Nowhere dense subsets of the fibres over a reduced irreducible base

Let `f : X ⟶ Y` be a morphism of finite type (`LocallyOfFiniteType` and `QuasiCompact`) with `Y`
reduced and irreducible, and let `Z ⊆ X` be closed. If the inverse image of `Z` under
`f.fiberι η : f.fiber η ⟶ X` is nowhere dense for the generic point `η` of `Y`, then its inverse
image in the fibre over every point of some nonempty open subset of `Y` is nowhere dense.

## References

* [Stacks Project, Tag 054X](https://stacks.math.columbia.edu/tag/054X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In a Noetherian quasi-sober space, a closed subset that is not nowhere dense contains a
generic point of an irreducible component. -/
private lemma exists_genericPoint_mem_of_not_isNowhereDense
    {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {A : Set T} (hA : IsClosed A) (hnd : ¬ IsNowhereDense A) :
    ∃ x : T, x ∈ A ∧ x ∈ genericPoints T := by
  have hne : interior A ≠ ∅ := fun he => hnd (by rwa [IsNowhereDense, hA.closure_eq])
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  let C : irreducibleComponents T :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let g : genericPoints T := genericPoints.ofComponent C
  have hspec : g.1 ⤳ x := specializes_iff_mem_closure.mpr <| by
    rw [genericPoints.isGenericPoint_ofComponent C]
    exact mem_irreducibleComponent
  exact ⟨g.1, interior_subset (hspec.mem_open isOpen_interior hx), g.2⟩

private alias genericPoint_mem_dense_open := _root_.mem_of_isGenericPoint_univ_of_dense

private alias exists_nat_fiber_dimensionAt_of_genericPoint :=
  exists_nat_topologicalKrullDimAt_fiber_of_mem_genericPoints

private lemma fiberPointAt_congr {X Y : Scheme.{u}} (f : X ⟶ Y)
    {x x' : X} (hxx : x = x') (y : Y) (h : f x = y) (h' : f x' = y) :
    Scheme.Hom.asFiberAt f x y h = Scheme.Hom.asFiberAt f x' y h' := by
  cases hxx; simp [Scheme.Hom.asFiberAt]

private lemma fiberPointAt_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) : f.fiberι y (Scheme.Hom.asFiberAt f x y h) = x := by
  cases h; exact f.fiberι_asFiber x

private lemma genericPoints_fiberPointAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y)
    (hx : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    Scheme.Hom.asFiberAt f x y h ∈ genericPoints (f.fiber y) := by cases h; exact hx

private lemma fiberPointAt_localDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber y) (Scheme.Hom.asFiberAt f x y h) := by cases h; rfl

/-- Fibres of a morphism locally of finite type are Noetherian spaces. -/
private lemma noetherianSpace_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) : NoetherianSpace (f.fiber y) :=
  have := isLocallyNoetherian_fiber_of_locallyOfFiniteType f y
  have : IsNoetherian (f.fiber y) := {}
  inferInstance

/-- If `f : X ⟶ Y` is of finite type with `Y` reduced and irreducible, `Z ⊆ X` is closed and the
inverse image of `Z` in the generic fibre is nowhere dense, then the inverse image of `Z` in the
fibre over every point of some nonempty open subset of `Y` is nowhere dense. -/
theorem exists_open_nowhereDense_fiber_of_reduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced Y] [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (Z : Set X) (hZ : IsClosed Z)
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hηZ : IsNowhereDense ((f.fiberι η) ⁻¹' Z)) :
    ∃ W : Set Y, IsOpen W ∧ W.Nonempty ∧
      ∀ y ∈ W, IsNowhereDense ((f.fiberι y) ⁻¹' Z) := by
  obtain ⟨U, V, hU, hV, hflatF, hfpF, hflatG, hfpG⟩ :=
    AlgebraicGeometry.exists_dense_opens_flat_source_and_closed f Z hZ
  have hηU : η ∈ U := genericPoint_mem_dense_open hη U.2 hU
  have hηV : η ∈ V := genericPoint_mem_dense_open hη V.2 hV
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩
  let i : I.subscheme ⟶ X := I.subschemeι
  let g : I.subscheme ⟶ Y := i ≫ f
  let UX : X.Opens := f ⁻¹ᵁ U
  let jX : UX.toScheme ⟶ X := UX.ι
  let fU : UX.toScheme ⟶ Y := jX ≫ f
  have hfacF : fU = f.resLE U UX le_rfl ≫ U.ι := (Scheme.Hom.resLE_comp_ι f le_rfl).symm
  let TV : I.subscheme.Opens := g ⁻¹ᵁ V
  let jT : TV.toScheme ⟶ I.subscheme := TV.ι
  let gV : TV.toScheme ⟶ Y := jT ≫ g
  have hfacG : gV = g.resLE V TV le_rfl ≫ V.ι := (Scheme.Hom.resLE_comp_ι g le_rfl).symm
  have : Flat (f.resLE U UX le_rfl) := hflatF
  have : FinitePresentation (f.resLE U UX le_rfl) := hfpF
  have : Flat (g.resLE V TV le_rfl) := hflatG
  have : FinitePresentation (g.resLE V TV le_rfl) := hfpG
  have : LocallyOfFinitePresentation (f.resLE U UX le_rfl) :=
    hfpF.locallyOfFinitePresentation
  have : LocallyOfFinitePresentation (g.resLE V TV le_rfl) :=
    hfpG.locallyOfFinitePresentation
  have : Flat fU := by rw [hfacF]; infer_instance
  have : LocallyOfFinitePresentation fU := by rw [hfacF]; infer_instance
  have : Flat gV := by rw [hfacG]; infer_instance
  have : LocallyOfFinitePresentation gV := by rw [hfacG]; infer_instance
  refine ⟨(U : Set Y) ∩ V, U.2.inter V.2, ⟨η, hηU, hηV⟩, ?_⟩
  rintro y ⟨hyU, hyV⟩
  let A : Set (f.fiber y) := (f.fiberι y) ⁻¹' Z
  have hAclosed : IsClosed A := hZ.preimage (f.fiberι y).continuous
  by_contra hnd
  have := noetherianSpace_fiber f y
  obtain ⟨p, hpA, hpgen⟩ :=
    exists_genericPoint_mem_of_not_isNowhereDense hAclosed hnd
  rcases hpt : f.fiberHomeo y p with ⟨x, hxy⟩
  have hfy : f x = y := by simpa using hxy
  have hxEq : x = f.fiberι y p := by
    have hval := congrArg (fun q : f ⁻¹' {y} => (q : X)) hpt
    calc
      x = (f.fiberHomeo y p : f ⁻¹' {y}) := hval.symm
      _ = f.fiberι y p := Scheme.Hom.fiberHomeo_apply f y p
  let yBase := y
  cases hfy
  let y : Y := f x
  have hpAsFiber : f.asFiber x = p := by
    apply (f.fiberι (f x)).isEmbedding.injective
    rw [Scheme.Hom.fiberι_asFiber]
    simp [hxEq]
  have hpgenX : f.asFiber x ∈ genericPoints (f.fiber y) := by
    simpa [hpAsFiber] using hpgen
  have hxU : x ∈ UX := by
    change f x ∈ U
    exact hyU
  let xU : (↑UX) := ⟨x, hxU⟩
  have hxUval : jX xU = x := rfl
  have hbaseX : fU xU = y := by
    change (jX ≫ f) xU = f x
    rw [Scheme.Hom.comp_apply]
    rw [hxUval]
  have hbasePX : f x = fU xU := by simpa [y] using hbaseX.symm
  have hmapX : Scheme.Hom.fiberMapComp jX f (fU xU) (fU.asFiber xU) =
      Scheme.Hom.asFiberAt f x (fU xU) hbasePX := by
    have hm := Scheme.Hom.fiberMapComp_asFiberAt jX f xU (fU xU) rfl
    have hcomp : f (jX xU) = fU xU := by
      simp [fU]
    have hp := fiberPointAt_congr f hxUval (fU xU) hcomp hbasePX
    simpa [Scheme.Hom.asFiberAt, fU] using hm.trans hp
  have hgenU : fU.asFiber xU ∈ genericPoints (fU.fiber (fU xU)) := by
    have htarget : Scheme.Hom.fiberMapComp jX f (fU xU) (fU.asFiber xU) ∈
        genericPoints (f.fiber (fU xU)) := by
      rw [hmapX]
      exact genericPoints_fiberPointAt f x (fU xU) hbasePX hpgenX
    exact mem_genericPoints_of_isOpenImmersion_apply
      (Scheme.Hom.fiberMapComp jX f (fU xU)) htarget
  obtain ⟨t, htZ⟩ : x ∈ Set.range i := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    simpa [A, hxEq] using hpA
  let tY : I.subscheme := t
  have hgt : g tY = f x := by
    simp [g, i, tY, htZ]
  have hxfBase : f x = g tY := hgt.symm
  have hmapT : Scheme.Hom.fiberMapComp i f (g tY) (g.asFiber tY) =
      Scheme.Hom.asFiberAt f x (g tY) hxfBase := by
    have hm := Scheme.Hom.fiberMapComp_asFiberAt i f tY (g tY) rfl
    have hcomp : f (i tY) = g tY := (Scheme.Hom.comp_apply i f tY).symm
    have hp := fiberPointAt_congr f htZ (g tY) hcomp hxfBase
    simpa [Scheme.Hom.asFiberAt, g] using hm.trans hp
  have hgenT : g.asFiber tY ∈ genericPoints (g.fiber (g tY)) := by
    have htarget : Scheme.Hom.fiberMapComp i f (g tY) (g.asFiber tY) ∈
        genericPoints (f.fiber (g tY)) := by
      rw [hmapT]
      exact genericPoints_fiberPointAt f x (g tY) hxfBase hpgenX
    exact AlgebraicGeometry.genericPoints_preimage_of_isClosedImmersion
      (Scheme.Hom.fiberMapComp i f (g tY)) htarget
  have htV : tY ∈ TV := by
    change g tY ∈ V
    rw [hgt]
    exact hyV
  let tV : (↑TV) := ⟨tY, htV⟩
  have hbaseT : gV tV = y := by
    change (jT ≫ g) tV = f x
    rw [Scheme.Hom.comp_apply]
    change g tY = f x
    exact hgt
  have htVval : jT tV = tY := rfl
  have hgtV : g tY = gV tV := hgt.trans hbaseT.symm
  have hmapV : Scheme.Hom.fiberMapComp jT g (gV tV) (gV.asFiber tV) =
      Scheme.Hom.asFiberAt g tY (gV tV) hgtV := by
    have hm := Scheme.Hom.fiberMapComp_asFiberAt jT g tV (gV tV) rfl
    have hcomp : g (jT tV) = gV tV := by
      simp [gV]
    have hp := fiberPointAt_congr g htVval (gV tV) hcomp hgtV
    simpa [Scheme.Hom.asFiberAt, gV] using hm.trans hp
  have hgenV : gV.asFiber tV ∈ genericPoints (gV.fiber (gV tV)) := by
    have htarget : Scheme.Hom.fiberMapComp jT g (gV tV) (gV.asFiber tV) ∈
        genericPoints (g.fiber (gV tV)) := by
      rw [hmapV]
      exact genericPoints_fiberPointAt g tY (gV tV) hgtV hgenT
    exact mem_genericPoints_of_isOpenImmersion_apply
      (Scheme.Hom.fiberMapComp jT g (gV tV)) htarget
  have hηy : η ⤳ f x := hη.specializes (Set.mem_univ _)
  obtain ⟨tηV, htSpec, htBase⟩ :=
    (Flat.generalizingMap gV) (show η ⤳ gV tV from by simpa [hbaseT] using hηy)
  let tη : I.subscheme := jT tηV
  have htηbase : g tη = η := by
    simpa [gV, jT, tη] using htBase
  have htSpecializes : tη ⤳ tY := by
    change jT tηV ⤳ t
    exact htSpec.map jT.continuous
  let xη : X := i tη
  have hxηbase : f xη = η := by
    simpa [g, i, xη, htηbase] using htηbase
  subst η
  have hxηU : xη ∈ UX := by
    change f xη ∈ U
    rw [hxηbase]
    exact hηU
  let xηU : (↑UX) := ⟨xη, hxηU⟩
  have hxSpecializes : xηU ⤳ xU := by
    apply specializes_iff_mem_closure.mpr
    have hxcl : x ∈ closure ({xη} : Set X) := by
      simpa [xη, tη, tY, htZ] using
        (specializes_iff_mem_closure.mp (htSpecializes.map i.continuous))
    have hxpre : xU ∈ UX.ι ⁻¹' closure ({xη} : Set X) := hxcl
    rw [UX.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      UX.ι.continuous] at hxpre
    have hpreimage : UX.ι ⁻¹' ({xη} : Set X) = ({xηU} : Set (↑UX)) := by
      ext z
      change UX.ι z = xη ↔ z = xηU
      exact ⟨fun hz => Subtype.ext hz, fun hz => congrArg Subtype.val hz⟩
    simpa only [hpreimage] using hxpre
  obtain ⟨dF, hdF⟩ :=
    exists_nat_fiber_dimensionAt_of_genericPoint fU hgenU
  obtain ⟨dG, hdG⟩ :=
    exists_nat_fiber_dimensionAt_of_genericPoint gV hgenV
  have hspecDimF :=
    topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints
      fU hxSpecializes hgenU
  have hspecDimG :=
    topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints
      gV htSpec hgenV
  have hopenDimFη := fiberDimensionAt_comp_openImmersion UX.ι f xηU
  have hopenDimFy := fiberDimensionAt_comp_openImmersion UX.ι f xU
  have hopenDimGη := fiberDimensionAt_comp_openImmersion TV.ι g tηV
  have hopenDimGy := fiberDimensionAt_comp_openImmersion TV.ι g tV
  have hdimFη :
      topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) =
        topologicalKrullDimAt (f.fiber y) (f.asFiber x) := by
    have hOpenFη :
        topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) =
          topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xηU))
            ((UX.ι ≫ f).asFiber xηU) := by
      convert hopenDimFη.symm using 1; rfl
    have hOpenFy :
        topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xU)) ((UX.ι ≫ f).asFiber xU) =
          topologicalKrullDimAt (f.fiber y) (f.asFiber x) := by
      convert hopenDimFy using 1; rfl
    have hspecDimF' :
        topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xηU))
            ((UX.ι ≫ f).asFiber xηU) =
          topologicalKrullDimAt ((UX.ι ≫ f).fiber ((UX.ι ≫ f) xU))
            ((UX.ι ≫ f).asFiber xU) := by
      simpa [fU, jX] using hspecDimF
    exact hOpenFη.trans (hspecDimF'.trans hOpenFy)
  have hdimGη :
      topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) =
        topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) := by
    have hOpenGη :
        topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) =
          topologicalKrullDimAt ((TV.ι ≫ g).fiber ((TV.ι ≫ g) tηV))
            ((TV.ι ≫ g).asFiber tηV) := by
      simpa [jT, tη] using hopenDimGη.symm
    have hOpenGy :
        topologicalKrullDimAt ((TV.ι ≫ g).fiber ((TV.ι ≫ g) tV))
            ((TV.ι ≫ g).asFiber tV) =
          topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) :=
      hopenDimGy
    have hspecDimG' :
        topologicalKrullDimAt ((TV.ι ≫ g).fiber ((TV.ι ≫ g) tηV))
            ((TV.ι ≫ g).asFiber tηV) =
          topologicalKrullDimAt ((TV.ι ≫ g).fiber ((TV.ι ≫ g) tV))
            ((TV.ι ≫ g).asFiber tV) := by
      simpa [gV, jT] using hspecDimG
    exact hOpenGη.trans (hspecDimG'.trans hOpenGy)
  have hgtY : g tY = y := hgt
  have hgtTV : g (jT tV) = y := by rw [htVval]; exact hgtY
  have hgenTV : Scheme.Hom.asFiberAt g (jT tV) y hgtTV ∈ genericPoints (g.fiber y) := by
    have hgenTval : g.asFiber (jT tV) ∈ genericPoints (g.fiber (g (jT tV))) := by
      have hb : g tY = g (jT tV) := congrArg g htVval.symm
      have hc := genericPoints_fiberPointAt g tY (g (jT tV)) hb hgenT
      have hp := fiberPointAt_congr g htVval.symm (g (jT tV)) hb rfl
      have hp' : Scheme.Hom.asFiberAt g tY (g (jT tV)) hb = g.asFiber (jT tV) := by
        simpa [Scheme.Hom.asFiberAt] using hp
      rw [← hp']
      exact hc
    exact genericPoints_fiberPointAt g (jT tV) y hgtTV hgenTval
  have hxfy : f x = y := rfl
  have hpgenXY : Scheme.Hom.asFiberAt f x y hxfy ∈ genericPoints (f.fiber y) :=
    genericPoints_fiberPointAt f x y hxfy hpgenX
  have hix : i (jT tV) = x := by rw [htVval]; exact htZ
  have hmapY : Scheme.Hom.fiberMapComp i f y (Scheme.Hom.asFiberAt g (jT tV) y hgtTV) =
      Scheme.Hom.asFiberAt f x y hxfy := by
    have hcomp : (i ≫ f) (jT tV) = y := by
      change f (i (jT tV)) = f x
      rw [hix]
    have hm := Scheme.Hom.fiberMapComp_asFiberAt i f (jT tV) y hcomp
    have htargetBase : f (i (jT tV)) = y := by rw [hix]
    have hp := fiberPointAt_congr f hix y htargetBase hxfy
    simpa [Scheme.Hom.asFiberAt, g] using hm.trans hp
  have htargetY : Scheme.Hom.fiberMapComp i f y (Scheme.Hom.asFiberAt g (jT tV) y hgtTV) ∈
      genericPoints (f.fiber y) := by
    rw [hmapY]
    exact hpgenXY
  have hdimAtYraw :=
    AlgebraicGeometry.topologicalKrullDimAt_eq_of_isClosedImmersion_genericPoints
      (Scheme.Hom.fiberMapComp i f y) (Y.residueField y) (g.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField y) hgenTV htargetY
  have hdimAtY :
      topologicalKrullDimAt (g.fiber y) (Scheme.Hom.asFiberAt g (jT tV) y hgtTV) =
        topologicalKrullDimAt (f.fiber y) (Scheme.Hom.asFiberAt f x y hxfy) := by
    simpa [g, hmapY] using hdimAtYraw
  have hdimGspecial := fiberPointAt_localDimension g (jT tV) y hgtTV
  have hdimFspecial := fiberPointAt_localDimension f x y hxfy
  have hdimη : topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) =
      topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := by
    calc
      _ = topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) := hdimGη
      _ = topologicalKrullDimAt (g.fiber y) (Scheme.Hom.asFiberAt g (jT tV) y hgtTV) :=
        hdimGspecial
      _ = topologicalKrullDimAt (f.fiber y) (Scheme.Hom.asFiberAt f x y hxfy) := hdimAtY
      _ = topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := hdimFspecial.symm
      _ = topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := hdimFη.symm
  have hdGspecial :
      topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) =
        (dG : WithBot ℕ∞) := hopenDimGy.symm.trans hdG
  have hfiniteGη :
      topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) ≠ ⊤ := by
    rw [hdimGη, hdGspecial]
    apply ne_of_lt
    apply WithBot.coe_lt_coe.mpr
    simp
  have hdFeta :
      topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) =
        (dG : WithBot ℕ∞) := by
    calc
      _ = topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) := hdimη.symm
      _ = topologicalKrullDimAt (g.fiber (g (jT tV))) (g.asFiber (jT tV)) := hdimGη
      _ = (dG : WithBot ℕ∞) := hdGspecial
  obtain ⟨B, hB, htηB, hBdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      (Y.residueField (f xη)) (g.fiber (f xη))
      (g.fiberToSpecResidueField (f xη))
      (Scheme.Hom.asFiberAt g tη (f xη) (htηbase.trans hxηbase.symm))
  let φ : g.fiber (f xη) ⟶ f.fiber (f xη) := Scheme.Hom.fiberMapComp i f (f xη)
  let D : Set (f.fiber (f xη)) := φ '' B
  have hBclosed : IsClosed B := isClosed_of_mem_irreducibleComponents B hB
  have hDclosed : IsClosed D := φ.isClosedEmbedding.isClosedMap B hBclosed
  have hDirr : IsIrreducible D := hB.1.image φ φ.continuous.continuousOn
  have hDdim : topologicalKrullDim D =
      topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := by
    have hhomeo : topologicalKrullDim D = topologicalKrullDim B :=
      ((φ.isEmbedding.homeomorphImage B).isHomeomorph.topologicalKrullDim_eq _).symm
    have hηbaseG : g tη = f xη := htηbase.trans hxηbase.symm
    have hηpoint : Scheme.Hom.asFiberAt g tη (f xη) hηbaseG ∈ B := htηB
    have hpoint : φ (Scheme.Hom.asFiberAt g tη (f xη) hηbaseG) = f.asFiber xη := by
      have hm := Scheme.Hom.fiberMapComp_asFiberAt i f tη (f xη) hηbaseG
      simpa [φ, Scheme.Hom.asFiberAt, g, xη] using hm
    have hdimGηAtPoint := fiberPointAt_localDimension g tη (f xη) hηbaseG
    calc
      topologicalKrullDim D = topologicalKrullDim B := hhomeo
      _ = topologicalKrullDimAt (g.fiber (f xη))
          (Scheme.Hom.asFiberAt g tη (f xη) hηbaseG) := hBdim
      _ = topologicalKrullDimAt (g.fiber (g tη)) (g.asFiber tη) := hdimGηAtPoint.symm
      _ = topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := hdimη
  have hxηD : f.asFiber xη ∈ D := by
    refine ⟨Scheme.Hom.asFiberAt g tη (f xη) (htηbase.trans hxηbase.symm), htηB, ?_⟩
    simpa [φ, Scheme.Hom.asFiberAt, g, xη] using
      (Scheme.Hom.fiberMapComp_asFiberAt i f tη (f xη) (htηbase.trans hxηbase.symm))
  obtain ⟨C, hC, hDC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible D hDirr
  have hxηC : f.asFiber xη ∈ C := hDC hxηD
  have := noetherianSpace_fiber f (f xη)
  have hCdimle :
      topologicalKrullDim C ≤ topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents
      (Y.residueField (f xη)) (f.fiber (f xη)) (f.fiberToSpecResidueField (f xη)) (f.asFiber xη)]
    exact le_iSup_of_le C (le_iSup_of_le ⟨hC, hxηC⟩ le_rfl)
  let D' : IrreducibleCloseds (f.fiber (f xη)) := ⟨D, hDirr, hDclosed⟩
  let C' : IrreducibleCloseds (f.fiber (f xη)) :=
    ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have hDC' : D' ≤ C' := hDC
  have hDfinite : topologicalKrullDim D ≠ ⊤ := by rwa [hDdim, ← hdimη]
  have hDeqC : D' = C' := by
    by_contra hne
    have hlt : D' < C' := lt_of_le_of_ne hDC' hne
    have hstrict :=
      topologicalKrullDim_lt_of_lt_irreducibleCloseds D' C' hlt
        (by simpa [D'] using hDfinite)
    have hstrict' : topologicalKrullDim D < topologicalKrullDim C := by
      simpa [D', C'] using hstrict
    have hstrictLocal :
        topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) < topologicalKrullDim C := by
      rwa [← hDdim]
    exact (not_lt_of_ge hCdimle) hstrictLocal
  have hsetEq : D = C := congrArg IrreducibleCloseds.carrier hDeqC
  have hDsubsetZ : D ⊆ (f.fiberι (f xη)) ⁻¹' Z := by
    rintro z ⟨z', hz', rfl⟩
    have hz := congrArg (fun q => q z') (Scheme.Hom.fiberMapComp_fiberι i f (f xη))
    change f.fiberι (f xη) (φ z') ∈ Z
    change f.fiberι (f xη) (φ z') = i ((i ≫ f).fiberι (f xη) z') at hz
    rw [hz]
    have hrange : i ((i ≫ f).fiberι (f xη) z') ∈ Set.range i :=
      ⟨(i ≫ f).fiberι (f xη) z', rfl⟩
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hrange
    exact hrange
  have hCsubsetZ : C ⊆ (f.fiberι (f xη)) ⁻¹' Z := by
    simpa [hsetEq] using hDsubsetZ
  let c : genericPoints (f.fiber (f xη)) := genericPoints.ofComponent ⟨C, hC⟩
  obtain ⟨O, hO, hOne, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({c.1} : Set (f.fiber (f xη)))) c.2
  have hc : closure ({c.1} : Set (f.fiber (f xη))) = C :=
    (genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩).def
  have hOA : O ⊆ (f.fiberι (f xη)) ⁻¹' Z := by
    rw [← hc] at hCsubsetZ
    exact hOC.trans hCsubsetZ
  have hIntNonempty : (interior ((f.fiberι (f xη)) ⁻¹' Z)).Nonempty := by
    obtain ⟨z, hz⟩ := hOne
    exact ⟨z, (hO.subset_interior_iff.mpr hOA) hz⟩
  have hempty : interior ((f.fiberι (f xη)) ⁻¹' Z) = ∅ := by
    have hηZ' := AlgebraicGeometry.isNowhereDense_fiberι_preimage_congr f (gV tηV) (f xη)
      hxηbase.symm Z hηZ
    rw [IsNowhereDense, (hZ.preimage (f.fiberι (f xη)).continuous).closure_eq] at hηZ'
    exact hηZ'
  exact (Set.nonempty_iff_ne_empty.mp hIntNonempty) hempty


end AlgebraicGeometry

end
