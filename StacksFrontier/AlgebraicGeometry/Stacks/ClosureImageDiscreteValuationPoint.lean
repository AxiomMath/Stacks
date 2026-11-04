module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.DiscreteValuationSpecialization
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Reaching a point in the closure by a discrete valuation ring

For a finite-type 1-morphism of algebraic stacks whose target is locally Noetherian, every point
in the closure of the image is the image of the closed point of a valuative square whose
valuation ring is a discrete valuation ring.

## Main results

* `AlgebraicGeometry.Stack.exists_discreteValuationRing_of_mem_closure_range_pointsMap`:
  **Stacks 0H2B**.

## Implementation notes

The diagram is packaged by `AlgebraicGeometry.Stack.ValuativeSquare`, as in the valuation-ring
statement of Stacks 0CL2; discreteness of the valuation ring is an extra clause, and membership
of the spectrum of the residue field at its closed point in the chosen big fppf site is a
separate existential, since nothing in the square mentions it.

The morphism is base changed twice, first to a locally Noetherian scheme chart of the target and
then to an affine Noetherian open of that chart, and an affine smooth presentation of the result
is chosen. Stacks 0CL2 supplies a point of the source whose image specializes to the prescribed
point, so the scheme morphism underlying the presentation is of finite type over a Noetherian
affine scheme and the prescribed point lies in the closure of its image; the diagram of
Stacks 0CM2, `AlgebraicGeometry.nonempty_discreteValuationSpecialization`, applies to it.

The valuation ring and fraction field so produced must be small enough for their spectra to lie
in the chosen big fppf site. That is `exists_small_discreteValuationSpecialization`: when the
chosen generic point already maps to the prescribed point the diagram is replaced by one built
from the local ring of an affine line at the origin, and otherwise the bound is read off the
identification of the fraction field with a residue field of the source.

## References

* [Stacks Project, Tag 0H2B](https://stacks.math.columbia.edu/tag/0H2B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

/-- A discrete-valuation-ring diagram reaching a point in the closure of the image can be chosen
with both its valuation ring and its fraction field small enough for their spectra to lie in the
chosen big fppf site. -/
private theorem exists_small_discreteValuationSpecialization
    (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y) (y : Y)
    (d : DiscreteValuationSpecialization f y) :
    ∃ d' : DiscreteValuationSpecialization f y,
      B.Contains (Spec (.of d'.fractionField)) ∧
      B.Contains (Spec (.of d'.valuationRing)) := by
  classical
  have hk := BigFppfSite.residueField_spec_contains B hX d.genericPoint
  by_cases heq : f.base d.genericPoint = y
  · let k : Type u := X.residueField d.genericPoint
    let _ : Field k := inferInstance
    let p : Ideal (Polynomial k) := Ideal.span {Polynomial.X}
    have hp : p ≠ ⊥ := by simp [p]
    let _ : p.IsPrime :=
      (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X
    let A := Localization.AtPrime p
    let K := FractionRing A
    let _ : IsDiscreteValuationRing A :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k) hp A
    let _ : Algebra A K := OreLocalization.instAlgebra
    have _ : IsFractionRing A K := inferInstance
    let r : k →+* A := (algebraMap (Polynomial k) A).comp Polynomial.C
    let i : A →+* K := algebraMap A K
    let a : Spec (.of A) ⟶ Spec (.of k) := Scheme.Spec.map (CommRingCat.ofHom r).op
    let b : Spec (.of K) ⟶ Spec (.of k) :=
      Scheme.Spec.map (CommRingCat.ofHom (i.comp r)).op
    have hcomm : Scheme.Spec.map (CommRingCat.ofHom i).op ≫ a = b := by
      simp [a, b]
    have hA : B.Contains (Spec (.of A)) :=
      Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
        p.primeCompl A (Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
          B.cutoff_isStrongPrelimit k (Polynomial k) hk)
    refine ⟨{
      valuationRing := A
      fractionField := K
      genericPoint := d.genericPoint
      component := d.component
      component_mem := d.component_mem
      isGenericPoint := d.isGenericPoint
      toSource := b ≫ X.fromSpecResidueField d.genericPoint
      toTarget := a ≫ X.fromSpecResidueField d.genericPoint ≫ f
      maps_genericPoint := by
        show X.fromSpecResidueField d.genericPoint (b _) = d.genericPoint
        exact Scheme.fromSpecResidueField_apply _ _
      maps_closedPoint := by
        show f (X.fromSpecResidueField d.genericPoint (a _)) = y
        rw [Scheme.fromSpecResidueField_apply]
        exact heq
      commutes := by
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ X.fromSpecResidueField d.genericPoint ≫ f) hcomm
      residueFieldEquiv := fun h => (h heq).elim },
      Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
        (nonZeroDivisors A) K hA, hA⟩
  · obtain ⟨e, -⟩ := d.residueFieldEquiv heq
    have hK : B.Contains (Spec (.of d.fractionField)) := by
      show (Spec (.of d.fractionField)).size < B.cutoff
      change (Spec (.of (X.residueField d.genericPoint))).size < B.cutoff at hk
      rw [Scheme.size_Spec] at hk ⊢
      simpa only [Cardinal.mk_congr e.toEquiv] using hk
    exact ⟨d, hK, Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit hK
      ((Cardinal.mk_le_of_injective (IsFractionRing.injective
        d.valuationRing d.fractionField)).trans (le_max_right _ _))⟩

/-- The image of the closed point of a represented spectrum under a 1-morphism of represented
categories fibred in groupoids has underlying scheme point the image of that point. -/
private theorem schemePoint_pointsMap_closedPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U W : BigFppfOver B S hS}
    (m : (schemeFibredCategory B S hS U).based ⥤ᵇ (schemeFibredCategory B S hS W).based)
    (z : U.left.1) (hz : B.Contains (Spec (.of (U.left.1.residueField z)))) :
    schemePoint B S hS W (pointsMap B S hS (schemeFibredCategory B S hS U).based
      (schemeFibredCategory B S hS U).property (schemeFibredCategory B S hS W).property m
      (pointClass B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property
        (closedPointFieldValuedPoint B S hS U z hz))) =
      (BigFppfOver.toScheme B S hS).map (schemeMapOfFunctor B S hS m) z := by
  rw [schemePoint_naturality]
  exact congrArg _ (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField_apply z _)

/-- A point in the closure of the image of a map lifts along an open map: if `b` is open, every
point of the image of `g` is `b` of a point in the range of `h`, and `b v = y` lies in the
closure of the range of `g`, then `v` is in the closure of the range of `h`. -/
private theorem mem_closure_range_of_isOpenMap_lift
    {A V Y W : Type*} [TopologicalSpace V] [TopologicalSpace Y]
    (b : V → Y) (g : A → Y) (h : W → V)
    (hbOpen : IsOpenMap b)
    (hLift : ∀ a v, g a = b v → ∃ w, h w = v)
    {y : Y} (hy : y ∈ closure (Set.range g)) {v : V} (hv : b v = y) :
    v ∈ closure (Set.range h) := by
  refine mem_closure_iff.mpr fun O hO hvO => ?_
  obtain ⟨z, ⟨v', hv'O, hbv'z⟩, a, hga⟩ :=
    mem_closure_iff.mp hy (b '' O) (hbOpen O hO) ⟨v, hvO, hv⟩
  obtain ⟨w, hww'⟩ := hLift a v' (hga.trans hbv'z.symm)
  exact ⟨h w, by simpa [hww'] using hv'O, ⟨w, rfl⟩⟩

/-- A point of a smooth chart lying over a point in the closure of the image of `f` lies in the
closure of the image of the base change of `f` to the chart. -/
private theorem mem_closure_range_pointsMap_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒱 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (b : 𝒱 ⟶ 𝒴)
    (hb : AlgebraicStacks.IsSmooth B S hS b)
    (P : Bicategory.TwoCommSq b f) (hP : Bicategory.IsTwoFibreProduct P)
    (y : AlgebraicStacks.points B S hS 𝒴) (v : AlgebraicStacks.points B S hS 𝒱)
    (hv : AlgebraicStacks.pointsMap B S hS b v = y)
    (hy : y ∈ @closure _ (pointTopology B S hS 𝒴.val)
      (Set.range (AlgebraicStacks.pointsMap B S hS f))) :
    v ∈ @closure _ (pointTopology B S hS 𝒱.val)
      (Set.range (AlgebraicStacks.pointsMap B S hS P.fst)) := by
  let _ := pointTopology B S hS 𝒴.val
  let _ := pointTopology B S hS 𝒱.val
  refine mem_closure_range_of_isOpenMap_lift _ _ _
    (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS b hb) ?_ hy hv
  intro x v' hxv
  obtain ⟨p, hp, -⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP v' x hxv.symm
  exact ⟨p, hp⟩

/-- The morphism of schemes underlying a 1-morphism of represented algebraic stacks which is
locally of finite type is itself locally of finite type. -/
theorem locallyOfFiniteType_schemeMapOfFunctor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W U : BigFppfOver B S hS}
    (b : schemeStack.{u, w} B S hS W ⟶ schemeStack.{u, w} B S hS U)
    (hb : AlgebraicStacks.IsLocallyOfFiniteType B S hS b) :
    LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (schemeMapOfFunctor B S hS b.hom.hom)) := by
  have hsome := (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS W).property (schemeStack.{u, w} B S hS U).property b.hom).1 hb
  have hrep := (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS W).property (schemeStack.{u, w} B S hS U).property
    (yoneda.obj W) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) b.hom).1 hsome
  rw [representingMap_eq_yoneda_map_baseMap B S hS b.hom.hom] at hrep
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget _).1 hrep

/-- A morphism of the site out of a scheme over `S`, as a morphism of site objects. -/
private def siteHom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (g : U.left.1 ⟶ V.left.1)
    (hg : g ≫ B.inclusion.map V.hom = B.inclusion.map U.hom) : U ⟶ V :=
  Over.homMk (⟨g⟩ : U.left ⟶ V.left) (B.inclusion.map_injective hg)

/-- **Stacks 0H2B.** A point in the closure of the image of a finite-type 1-morphism of algebraic
stacks whose target is locally Noetherian is reached by the closed point of a valuative square
whose valuation ring is a discrete valuation ring. -/
@[stacks 0H2B]
theorem exists_discreteValuationRing_of_mem_closure_range_pointsMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFiniteType B S hS f)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (y : points B S hS 𝒴.val.val (Classical.choose 𝒴.property))
    (hy : y ∈ @closure _
      (pointTopology B S hS 𝒴.val)
      (Set.range
        (pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
          (Classical.choose 𝒴.property) f.hom.hom))) :
    ∃ (q : ValuativeSquare B S hS f) (_ : IsDiscreteValuationRing q.R)
      (hz : B.Contains
        (Spec (.of ((Spec (.of q.R)).residueField (IsLocalRing.closedPoint q.R))))),
      pointClass B S hS 𝒴.val.val
        (Classical.choose 𝒴.property)
        (fieldValuedPointMap B S hS
          (schemeFibredCategory B S hS
            (siteObject B S hS q.ring_mem q.base)).val
          q.y.hom
          (closedPointFieldValuedPoint B S hS
            (siteObject B S hS q.ring_mem q.base)
            (IsLocalRing.closedPoint q.R) hz)) = y := by
  classical
  let T := BigFppfOver.toScheme B S hS
  -- a smooth surjective chart of `𝒴` by a locally Noetherian scheme
  obtain ⟨V, bStack, hbsurj, hbsm, hV⟩ := h𝒴
  obtain ⟨v, hv⟩ := hbsurj y
  -- the base change of `f` to that chart
  let P := twoFibreProductSquareAlgebraicStacks B S hS bStack f
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bStack f
  have hf' := AlgebraicStacks.isFiniteType_baseChange B S hS f bStack P hP hf
  have hv' := mem_closure_range_pointsMap_baseChange B S hS f bStack hbsm P hP y v hv hy
  let z : T.obj V := schemePoint B S hS V v
  -- Stacks 0CL2 locates a point of the base change whose image specializes to `z`
  obtain ⟨q₀, hz₀, hclosed₀⟩ :=
    exists_valuationRing_of_mem_closure_range_pointsMap B S hS P.fst hf'.2 v hv'
  have hgen : ∃ x : AlgebraicStacks.points B S hS P.pt,
      schemePoint B S hS V (AlgebraicStacks.pointsMap B S hS P.fst x) ⤳ z := by
    let Robj := siteObject B S hS q₀.ring_mem q₀.base
    let Kobj := siteObject B S hS q₀.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q₀.R q₀.K)) ≫ q₀.base)
    obtain ⟨p, -⟩ := schemePoint_surjective B S hS Kobj (IsLocalRing.closedPoint q₀.K)
    refine ⟨pointsMap B S hS _ (schemeFibredCategory B S hS Kobj).property
      (Classical.choose P.pt.property) q₀.x.hom p, ?_⟩
    have hc := congrFun (pointsMap_eq_of_basedNatTrans B S hS
      (schemeFibredCategory B S hS Kobj).val (schemeFibredCategory B S hS Kobj).property
      (Classical.choose (schemeStack.{u, w} B S hS V).property) q₀.γ.hom) p
    have h1 := pointsMap_comp B S hS (schemeFibredCategory B S hS Kobj).val
      (schemeFibredCategory B S hS Kobj).property (Classical.choose P.pt.property)
      (Classical.choose (schemeStack.{u, w} B S hS V).property) q₀.x.hom P.fst.hom.hom p
    have h2 := pointsMap_comp B S hS (schemeFibredCategory B S hS Kobj).val
      (schemeFibredCategory B S hS Kobj).property
      (schemeFibredCategory B S hS Robj).property
      (Classical.choose (schemeStack.{u, w} B S hS V).property) q₀.j.hom q₀.y.hom p
    have hchain : AlgebraicStacks.pointsMap B S hS P.fst
          (pointsMap B S hS _ (schemeFibredCategory B S hS Kobj).property
            (Classical.choose P.pt.property) q₀.x.hom p) =
        pointsMap B S hS (schemeFibredCategory B S hS Robj).val
          (schemeFibredCategory B S hS Robj).property
          (Classical.choose (schemeStack.{u, w} B S hS V).property) q₀.y.hom
          (pointsMap B S hS _ (schemeFibredCategory B S hS Kobj).property
            (schemeFibredCategory B S hS Robj).property q₀.j.hom p) :=
      h1.trans (hc.symm.trans h2.symm)
    have hzeq : z = T.map (schemeMapOfFunctor B S hS q₀.y.hom)
        (IsLocalRing.closedPoint q₀.R) := by
      rw [show z = schemePoint B S hS V v from rfl, ← hclosed₀]
      exact schemePoint_pointsMap_closedPoint B S hS (U := Robj) (W := V) q₀.y.hom
        (IsLocalRing.closedPoint q₀.R) hz₀
    rw [hchain, schemePoint_naturality, hzeq]
    exact (IsLocalRing.specializes_closedPoint _).map
      (T.map (schemeMapOfFunctor B S hS q₀.y.hom)).continuous
  -- an affine Noetherian open neighbourhood of `z` in the chart
  let _ : IsLocallyNoetherian (T.obj V) := hV
  obtain ⟨O, hO, hzO, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) (by simp)
  let Osite : B.Schemes :=
    ⟨(O : Scheme.{u}), (Scheme.size_coe_opens_le (T.obj V) O).trans_lt V.left.property⟩
  let isite : Osite ⟶ V.left := ⟨O.ι⟩
  let Vaff : BigFppfOver B S hS := Over.mk (isite ≫ V.hom)
  let jsite : Vaff ⟶ V := Over.homMk isite
  let jStack : schemeStack.{u, w} B S hS Vaff ⟶ schemeStack.{u, w} B S hS V :=
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS jsite)
  have hjmap : schemeMapOfFunctor B S hS jStack.hom.hom = jsite :=
    schemeMapOfFunctor_overMapBased B S hS jsite
  have hjpt : ∀ t u, schemePoint B S hS V u = (schemePoint B S hS Vaff t).1 →
      AlgebraicStacks.pointsMap B S hS jStack t = u := fun t u h => by
    apply schemePoint_injective B S hS V
    rw [schemePoint_naturality, hjmap]
    exact h.symm
  let _ : IsAffine (T.obj Vaff) := hO
  let _ : IsLocallyNoetherian (T.obj Vaff) := isLocallyNoetherian_of_isOpenImmersion O.ι
  -- the base change to the affine chart, and an affine smooth presentation of it
  let Q := twoFibreProductSquareAlgebraicStacks B S hS jStack P.fst
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS jStack P.fst
  have hQft := AlgebraicStacks.isFiniteType_baseChange B S hS P.fst jStack Q hQ hf'
  have hQqc := hf'.2 (schemeStack.{u, w} B S hS Vaff) jStack
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS Vaff hO)
  obtain ⟨W, hW, aStack, haSurj, haSm⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS Q.pt).1 hQqc
  let _ : IsAffine (T.obj W) := hW
  have hidlft : Space.IsLocallyOfFiniteType B S hS (𝟙 (yoneda.obj W)) := by
    simpa using (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (𝟙 W)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have haft : AlgebraicStacks.IsLocallyOfFiniteType B S hS aStack :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (schemeStack.{u, w} B S hS W).property Q.pt.property aStack.hom).2
      (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
        (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h) aStack.hom
        (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
        (PresheafOfCategories.sliceElementsEquivalenceOver W) haSm hidlft)
  let c : schemeStack.{u, w} B S hS W ⟶ schemeStack.{u, w} B S hS Vaff := aStack ≫ Q.fst
  let k : W ⟶ Vaff := schemeMapOfFunctor B S hS c.hom.hom
  let _ : LocallyOfFiniteType (T.map k) :=
    locallyOfFiniteType_schemeMapOfFunctor B S hS c
      (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS aStack Q.fst haft hQft.1)
  let _ : QuasiCompact (T.map k) := inferInstance
  let zaff : T.obj Vaff := ⟨z, hzO⟩
  -- the chosen point is in the closure of the image of the scheme morphism
  have hcl : zaff ∈ closure (Set.range (T.map k).base) := by
    obtain ⟨x, hx⟩ := hgen
    let zgen : T.obj Vaff :=
      ⟨schemePoint B S hS V (AlgebraicStacks.pointsMap B S hS P.fst x),
        hx.mem_open O.isOpen hzO⟩
    obtain ⟨tgen, htgen⟩ := schemePoint_surjective B S hS Vaff zgen
    have ht := hjpt tgen _ (by rw [htgen])
    obtain ⟨xQ, hxQ, -⟩ :=
      exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Q hQ tgen x ht
    obtain ⟨xW, hxW⟩ := haSurj xQ
    have hcxW : AlgebraicStacks.pointsMap B S hS c xW = tgen := by
      rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hxW]
      exact hxQ
    have hkx : (T.map k).base (schemePoint B S hS W xW) = zgen := by
      calc (T.map k).base (schemePoint B S hS W xW)
          = schemePoint B S hS Vaff (AlgebraicStacks.pointsMap B S hS c xW) :=
            (schemePoint_naturality B S hS c.hom.hom xW).symm
        _ = zgen := by rw [hcxW, htgen]
    have hspec : zgen ⤳ zaff := Topology.IsInducing.subtypeVal.specializes_iff.mp hx
    exact hspec.mem_closed isClosed_closure (subset_closure ⟨_, hkx⟩)
  obtain ⟨vaff, hvaff⟩ := schemePoint_surjective B S hS Vaff zaff
  obtain ⟨d₀⟩ := nonempty_discreteValuationSpecialization (T.map k) zaff hcl
  obtain ⟨d, hdK, hdR⟩ :=
    exists_small_discreteValuationSpecialization B W.left.property (T.map k) zaff d₀
  -- the discrete valuation ring diagram, read as a valuative square for `f`
  let A := d.valuationRing
  let Kf := d.fractionField
  let gen := Spec.map (CommRingCat.ofHom (algebraMap A Kf))
  let base : Spec (.of A) ⟶ S := d.toTarget ≫ B.inclusion.map Vaff.hom
  let Aobj := siteObject B S hS hdR base
  let Kobj := siteObject B S hS hdK (gen ≫ base)
  have hkbase : T.map k ≫ B.inclusion.map Vaff.hom = B.inclusion.map W.hom :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w k))
  let hOver : Aobj ⟶ Vaff := siteHom B S hS d.toTarget rfl
  let jOver : Kobj ⟶ Aobj := siteHom B S hS gen rfl
  let kOver : Kobj ⟶ W := siteHom B S hS d.toSource (by
    rw [← hkbase, ← Category.assoc, ← d.commutes]
    rfl)
  let jCat := schemeFibredCategoryMap B S hS jOver
  let hCat := schemeFibredCategoryMap B S hS hOver
  let kCat := schemeFibredCategoryMap B S hS kOver
  have hhmap : schemeMapOfFunctor B S hS hCat.hom = hOver :=
    schemeMapOfFunctor_overMapBased B S hS hOver
  have hj : schemeMapOfFunctor B S hS (jCat ≫ hCat).hom = jOver ≫ hOver :=
    (schemeMapOfFunctor_comp_overMapBased B S hS jOver (overMapBased B S hS hOver)).trans
      (congrArg (fun t => jOver ≫ t) (schemeMapOfFunctor_overMapBased B S hS hOver))
  have hkc : schemeMapOfFunctor B S hS (kCat ≫ c.hom).hom =
      kOver ≫ schemeMapOfFunctor B S hS c.hom.hom :=
    schemeMapOfFunctor_comp_overMapBased B S hS kOver c.hom.hom
  have hmaps : schemeMapOfFunctor B S hS (jCat ≫ hCat).hom =
      schemeMapOfFunctor B S hS (kCat ≫ c.hom).hom := by
    rw [hj, hkc]
    exact Over.OverMorphism.ext (B.inclusion.map_injective d.commutes)
  let fill : (jCat ≫ hCat) ⟶ (kCat ≫ c.hom) :=
    Bicategory.InducedBicategory.mkHom₂ (basedNatTransOfSchemeMapEq B S hS _ _ hmaps)
  let bTotal : schemeStack.{u, w} B S hS Vaff ⟶ 𝒴 := jStack ≫ bStack
  let aTotal : schemeStack.{u, w} B S hS W ⟶ 𝒳 := aStack ≫ (Q.snd ≫ P.snd)
  let outer : (c.hom ≫ bTotal.hom) ⟶ (aTotal.hom ≫ f.hom) :=
    (α_ aStack.hom Q.fst.hom bTotal.hom).hom ≫
      (aStack.hom ◁ ((α_ Q.fst.hom jStack.hom bStack.hom).inv ≫
        (Q.iso.hom.hom ▷ bStack.hom) ≫ (α_ Q.snd.hom P.fst.hom bStack.hom).hom ≫
        (Q.snd.hom ◁ P.iso.hom.hom) ≫ (α_ Q.snd.hom P.snd.hom f.hom).inv)) ≫
      (α_ aStack.hom (Q.snd.hom ≫ P.snd.hom) f.hom).inv
  have hres := BigFppfSite.residueField_spec_contains B hdR (IsLocalRing.closedPoint A)
  refine ⟨{
    R := A
    K := Kf
    ring_mem := hdR
    field_mem := hdK
    base := base
    genericMap := jOver
    genericMap_left := rfl
    j := jCat
    j_canonical := rfl
    x := kCat ≫ aTotal.hom
    y := hCat ≫ bTotal.hom
    γ := (α_ jCat hCat bTotal.hom).inv ≫ (fill ▷ bTotal.hom) ≫
      (α_ kCat c.hom bTotal.hom).hom ≫ (kCat ◁ outer) ≫
      (α_ kCat aTotal.hom f.hom).inv }, d.isDVR, hres, ?_⟩
  -- the closed point of the valuation spectrum lands on `y`
  let special := pointClass B S hS (schemeFibredCategory B S hS Aobj).val
    (schemeFibredCategory B S hS Aobj).property
    (closedPointFieldValuedPoint B S hS Aobj (IsLocalRing.closedPoint A) hres)
  have hAV : pointsMap B S hS (schemeFibredCategory B S hS Aobj).val
      (schemeFibredCategory B S hS Aobj).property
      (Classical.choose (schemeStack.{u, w} B S hS Vaff).property) hCat.hom special = vaff := by
    apply schemePoint_injective B S hS Vaff
    refine (schemePoint_pointsMap_closedPoint B S hS (U := Aobj) (W := Vaff) hCat.hom
      (IsLocalRing.closedPoint A) hres).trans ?_
    rw [hhmap, hvaff]
    exact d.maps_closedPoint
  have hVy : AlgebraicStacks.pointsMap B S hS (jStack ≫ bStack) vaff = y := by
    rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, ← hv,
      hjpt vaff v (by rw [hvaff])]
  show pointsMap B S hS (schemeFibredCategory B S hS Aobj).val
    (schemeFibredCategory B S hS Aobj).property
    (Classical.choose 𝒴.property) (hCat ≫ bTotal.hom).hom special = y
  refine Eq.trans (pointsMap_comp B S hS (schemeFibredCategory B S hS Aobj).val
    (schemeFibredCategory B S hS Aobj).property
    (Classical.choose (schemeStack.{u, w} B S hS Vaff).property)
    (Classical.choose 𝒴.property) hCat.hom bTotal.hom.hom special).symm ?_
  rw [hAV]
  exact hVy

end AlgebraicGeometry.Stack

end
