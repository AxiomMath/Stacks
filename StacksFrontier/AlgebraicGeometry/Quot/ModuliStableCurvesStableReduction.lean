module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesAssembly
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionExistencePoints

/-!
# Stable reduction and the valuative hypothesis for `𝓜_g ⊂ 𝓜̄_g` (towards Stacks 0E9C)

The proof of **Stacks 0E9C** applies Stacks 0CQM to `𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)`, and says that what
remains to be checked — that every 2-commutative diagram
```
Spec K ---> 𝓜_g ---> 𝓜̄_g
  |                    |
  v                    v
Spec A ------------> Spec(ℤ)
```
with `A` a discrete valuation ring with fraction field `K` admits a dotted arrow after an extension
`K'/K` and a valuation ring `A' ⊂ K'` dominating `A` — is, after unwinding the moduli
interpretations of `𝓜_g` and `𝓜̄_g`, exactly the stable reduction theorem (Stacks 0E98). This file
carries out that unwinding.

## Main definitions

* `AlgebraicGeometry.StableReductionExtension`: the conclusion of part (1) of Stacks 0E98 for a
  family `F` of `𝓜_g` over `Spec K`, read in families of curves: an extension of discrete valuation
  rings `A ⊂ A'` inducing a finite separable extension `K'/K` of fraction fields, a family `G` of
  `𝓜̄_g` over `Spec A'` and a family `H` over `Spec K'` with cartesian morphisms `H ⟶ G` over
  `Spec K' ⟶ Spec A'` and `H ⟶ F` over `Spec K' ⟶ Spec K`, i.e. `G_{K'} ≅ H ≅ F_{K'}`.
* `AlgebraicGeometry.HasStableReductionCurveFamilies`: every family of `𝓜_g` over the fraction
  field of a discrete valuation ring admits such data. This is the reading of Stacks 0E98 (1) in
  the families parametrized by `𝓜_g` and `𝓜̄_g`.

## Main results

* `AlgebraicGeometry.denseTestExistence_moduliSmoothCurves_of_stableReduction`: the hypothesis of
  Stacks 0CQM for `𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)`, from `AlgebraicGeometry.HasStableReductionCurveFamilies`.
* `AlgebraicGeometry.moduliStableCurves_isDeligneMumford_proper_smooth_of_stableReduction`: the
  assembly of Stacks 0E9C with that hypothesis in place of the valuative one, the other inputs
  being explicit hypotheses (as in
  `AlgebraicGeometry.moduliStableCurves_isDeligneMumford_proper_smooth_of`).

## Implementation notes

The generic point `Spec K ⟶ 𝓜_g` of a valuative square is, by the 2-Yoneda lemma, its value `F` at
the unit object, a family of curves over `Spec K`. Stable reduction gives `A'`, `K'`, `G` and `H`;
the dominating extension is the canonical one of `A ⟶ A'`
(`AlgebraicGeometry.Stack.dominatingExtensionOfRingMaps`), and a dotted arrow is produced from a
span `Z_{K'} ⟶ F`, `Z_{K'} ⟶ Z_{A'}` in `𝓜̄_g` by
`AlgebraicGeometry.Stack.nonempty_dottedArrow_of_span`. The objects `Z_{A'}`, `Z_{K'}` are lifts
of `G` and `H` along the identifications of their bases with the spectra of the extension, and the
legs of the span are the given morphisms `H ⟶ F`, `H ⟶ G` transported along those lifts. The
special point of the square lands in `Spec(ℤ)`, represented by the terminal object, so the morphism
of the span over `Spec A' ⟶ Spec A` there and the compatibility with the link of the square are
forced: morphisms of `Spec(ℤ)` over a given morphism of the site are unique.

## References

* [Stacks Project, Tag 0E9C](https://stacks.math.columbia.edu/tag/0E9C)
* [Stacks Project, Tag 0E98](https://stacks.math.columbia.edu/tag/0E98)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0CLA](https://stacks.math.columbia.edu/tag/0CLA)
* [Stacks Project, Tag 0CLD](https://stacks.math.columbia.edu/tag/0CLD)
-/

@[expose] public section

open CategoryTheory Topology

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The conclusion of Stacks 0E98, part (1), read in families of curves.** Let `A` be a discrete
valuation ring with fraction field `K`, with structure morphism `tA : Spec A ⟶ Spec(ℤ)`, and let
`F` be a family of curves whose base is identified with `Spec K` by `e`. The data: an extension of
discrete valuation rings `A ⟶ A'` (a local homomorphism) inducing a finite separable extension
`K ⟶ K'` of fraction fields, both spectra in the big fppf site, a stable family of curves `G` of
genus `g` over `Spec A'`, and a family `H` over `Spec K'` with morphisms of families (cartesian
squares) `H ⟶ G` over the canonical `Spec K' ⟶ Spec A'` and `H ⟶ F` over `Spec K' ⟶ Spec K`; so
`G_{K'} ≅ H ≅ F_{K'}` over `K'`. -/
structure StableReductionExtension (g : ℕ) (A : Type u) [CommRing A] (K : Type u) [Field K]
    [Algebra A K] (hK : B.Contains (Spec (.of K))) (tA : Spec (.of A) ⟶ integerBase)
    (F : CurveFamily B hZ)
    (e : F.base ≅ siteObject B integerBase hZ hK
      (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ tA)) where
  /-- The extended discrete valuation ring. -/
  A' : Type u
  [commRing : CommRing A']
  [domain : IsDomain A']
  [isDiscreteValuationRing : IsDiscreteValuationRing A']
  /-- Its fraction field. -/
  K' : Type u
  [field : Field K']
  [algebra : Algebra A' K']
  [isFractionRing : IsFractionRing A' K']
  /-- The extension of discrete valuation rings. -/
  ringMap : A →+* A'
  /-- The induced extension of fraction fields. -/
  fieldMap : K →+* K'
  /-- The extension of discrete valuation rings is local. -/
  isLocalHom : IsLocalHom ringMap
  /-- The two maps are compatible with the inclusions of the rings in their fraction fields. -/
  fraction_comm : (algebraMap A' K').comp ringMap = fieldMap.comp (algebraMap A K)
  /-- The extension of fraction fields is finite. -/
  finite : fieldMap.Finite
  /-- The extension of fraction fields is separable. -/
  separable : letI := fieldMap.toAlgebra; Algebra.IsSeparable K K'
  /-- The spectrum of `A'` lies in the big fppf site. -/
  ring_mem : B.Contains (Spec (.of A'))
  /-- The spectrum of `K'` lies in the big fppf site. -/
  field_mem : B.Contains (Spec (.of K'))
  /-- The stable family over `Spec A'`. -/
  stable : CurveFamily B hZ
  /-- It is a stable family of curves of genus `g`. -/
  isStable : IsStableGenusCurveFamily B hZ g stable
  /-- Its base is `Spec A'`. -/
  stableBase : stable.base ≅
    siteObject B integerBase hZ ring_mem (Spec.map (CommRingCat.ofHom ringMap) ≫ tA)
  /-- The common base change of `F` and of the stable family to `Spec K'`. -/
  generic : CurveFamily B hZ
  /-- Its base is `Spec K'`. -/
  genericBase : generic.base ≅ siteObject B integerBase hZ field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap A' K')) ≫ Spec.map (CommRingCat.ofHom ringMap) ≫ tA)
  /-- The cartesian square identifying it with the generic fibre of the stable family. -/
  toStable : generic ⟶ stable
  /-- That square lies over the canonical morphism `Spec K' ⟶ Spec A'`. -/
  toStable_base : B.inclusion.map (genericBase.inv ≫ toStable.baseMap ≫ stableBase.hom).left =
    Spec.map (CommRingCat.ofHom (algebraMap A' K'))
  /-- The cartesian square identifying it with the base change of `F`. -/
  toGiven : generic ⟶ F
  /-- That square lies over `Spec K' ⟶ Spec K`. -/
  toGiven_base : B.inclusion.map (genericBase.inv ≫ toGiven.baseMap ≫ e.hom).left =
    Spec.map (CommRingCat.ofHom fieldMap)

attribute [instance] StableReductionExtension.commRing StableReductionExtension.domain
  StableReductionExtension.isDiscreteValuationRing StableReductionExtension.field
  StableReductionExtension.algebra StableReductionExtension.isFractionRing

/-- **Stacks 0E98, part (1), read in the families of `𝓜_g` and `𝓜̄_g`.** For every discrete
valuation ring `A` with fraction field `K` (both spectra in the big fppf site) and every family of
curves `F` over `Spec K` which is smooth with `H⁰ = K` fibrewise and of genus `g` (the families of
`𝓜_g`, Stacks 0E83), there are an extension of discrete valuation rings `A ⊂ A'` inducing a finite
separable extension `K'/K` and a stable family of genus `g` over `Spec A'` whose base change to
`K'` is isomorphic to `F_{K'}` (`AlgebraicGeometry.StableReductionExtension`). -/
def HasStableReductionCurveFamilies (g : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (_ : B.Contains (Spec (.of A))) (hK : B.Contains (Spec (.of K)))
    (tA : Spec (.of A) ⟶ integerBase) (F : CurveFamily B hZ)
    (e : F.base ≅ siteObject B integerBase hZ hK
      (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ tA)),
    IsSmoothGenusCurveFamily B hZ g F →
      Nonempty (StableReductionExtension B hZ g A K hK tA F e)

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

open Stack in
/-- **The valuative hypothesis of Stacks 0CQM for `𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)`, from stable
reduction.** If every family of `𝓜_g` over the fraction field of a discrete valuation ring has
stable reduction after a finite separable extension (Stacks 0E98, part (1), in the reading
`AlgebraicGeometry.HasStableReductionCurveFamilies`), then every valuative square for
`𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)` over a discrete valuation ring admits a dotted arrow for the induced square
for `𝓜̄_g ⟶ Spec(ℤ)` after an extension of the fraction field and passage to a dominating valuation
ring. This is the unwinding in the proof of Stacks 0E9C. -/
theorem denseTestExistence_moduliSmoothCurves_of_stableReduction (g : ℕ)
    (hP : IsOpenCurvesLocus B hZ (IsStableGenusCurveFamily B hZ g))
    (hQ : IsOpenCurvesLocus B hZ (IsSmoothGenusCurveFamily B hZ g))
    (hle : (curvesSmallOpenSubstack B hZ h hQ).property ≤
      (curvesSmallOpenSubstack B hZ h hP).property)
    (hred : HasStableReductionCurveFamilies B hZ g) :
    ValuativeCriterion.DenseTestExistence B integerBase hZ
      (OpenSubstack.homOfLE B integerBase hZ (curvesSmallOpenSubstack B hZ h hQ)
        (curvesSmallOpenSubstack B hZ h hP) hle)
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) := by
  let := locallySmall_curveFamily B hZ
  intro q hq
  let q' := ValuativeSquare.compRight B integerBase hZ q
  let X0 := q.x.hom.obj (Over.mk (𝟙 _))
  let F : CurveFamily B hZ := ShrinkHoms.fromShrinkHoms X0.obj
  have hF : IsSmoothGenusCurveFamily B hZ g F :=
    (curvesSmallOpenSubstack_property_iff B hZ h hQ F).1 X0.property
  have hbase : F.base = siteObject B integerBase hZ q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
    Functor.congr_obj q.x.hom.w (Over.mk (𝟙 _))
  obtain ⟨d⟩ := hred q.R q.K q.ring_mem q.field_mem q.base F (eqToIso hbase) hF
  let e := dominatingExtensionOfRingMaps B q' d.A' d.K' d.ringMap d.fieldMap d.isLocalHom
    d.fraction_comm d.ring_mem d.field_mem
  refine ⟨e, ?_⟩
  let Mbar := (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack
  let p := Mbar.val.val.p
  have hp := Mbar.val.isFiberedInGroupoids
  let X1 : Mbar.val.val.obj := q'.x.hom.obj (Over.mk (𝟙 _))
  let G' : Mbar.val.val.obj := ⟨ShrinkHoms.toShrinkHoms d.stable,
    (curvesSmallOpenSubstack_property_iff B hZ h hP d.stable).2 d.isStable⟩
  let H' : Mbar.val.val.obj := ⟨ShrinkHoms.toShrinkHoms d.generic,
    (curvesSmallOpenSubstack_property_iff B hZ h hP d.generic).2
      (hP.prop_of_hom d.toStable d.isStable)⟩
  let m0 : H' ⟶ G' := ObjectProperty.homMk ((ShrinkHoms.functor _).map d.toStable)
  let n0 : H' ⟶ X1 := ObjectProperty.homMk ((ShrinkHoms.functor _).map d.toGiven)
  have hm0 : p.map m0 = d.toStable.baseMap :=
    congrArg CurveFamily.Hom.baseMap ((equivShrink _).symm_apply_apply d.toStable)
  have hn0 : p.map n0 = d.toGiven.baseMap :=
    congrArg CurveFamily.Hom.baseMap ((equivShrink _).symm_apply_apply d.toGiven)
  have hm0l : p.IsHomLift d.toStable.baseMap m0 := hm0 ▸ IsHomLift.map p m0
  have hn0l : p.IsHomLift d.toGiven.baseMap n0 := hn0 ▸ IsHomLift.map p n0
  obtain ⟨ZR, cR, hcR⟩ := hp.exists_lift d.stableBase.inv G' rfl
  obtain ⟨ZK, cK, hcK⟩ := hp.exists_lift d.genericBase.inv H' rfl
  have hcRc : p.IsStronglyCartesian d.stableBase.inv cR :=
    hp.isStronglyCartesian_homLift d.stableBase.inv cR
  have hgo : (d.genericBase.inv ≫ d.toGiven.baseMap) ≫ eqToHom hbase = e.genericOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    refine Eq.trans ?_ e.genericOver_left.symm
    exact (congrArg (fun t => B.inclusion.map (Over.Hom.left t)) (Category.assoc _ _ _)).trans
      d.toGiven_base
  have hn : p.IsHomLift e.genericOver (cK ≫ n0) := hgo ▸
    @IsHomLift.lift_comp_eqToHom _ _ _ _ p _ _ _ _ (d.genericBase.inv ≫ d.toGiven.baseMap)
      (cK ≫ n0) (@IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hcK hn0l) _ hbase
  have hgm' : d.genericBase.inv ≫ d.toStable.baseMap ≫ d.stableBase.hom = e.genericMap := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    exact d.toStable_base.trans e.genericMap_left.symm
  have hgm : d.genericBase.inv ≫ d.toStable.baseMap = e.genericMap ≫ d.stableBase.inv :=
    (Iso.eq_comp_inv d.stableBase).2 (by rw [Category.assoc]; exact hgm')
  have hm1 : p.IsHomLift (d.genericBase.inv ≫ d.toStable.baseMap) (cK ≫ m0) :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hcK hm0l
  let m := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ d.stableBase.inv cR hcRc _ _ _ _
    hgm (cK ≫ m0) hm1
  have hm : p.IsHomLift e.genericMap m :=
    @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ d.stableBase.inv cR hcRc _ _ _ _
      hgm (cK ≫ m0) hm1
  let fM := (curvesSmallOpenSubstack B hZ h hP).inclusion ≫
    structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)
  let Y := schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))
  have hsrc : Y.val.val.p.obj (fM.hom.hom.obj ZR) =
      siteObject B integerBase hZ d.ring_mem (Spec.map (CommRingCat.ofHom d.ringMap) ≫ q.base) :=
    (Functor.congr_obj fM.hom.hom.w ZR).trans (IsHomLift.domain_eq p d.stableBase.inv cR)
  have htgt : Y.val.val.p.obj (q'.y.hom.obj (Over.mk (𝟙 _))) =
      siteObject B integerBase hZ q.ring_mem q.base :=
    Functor.congr_obj q'.y.hom.w (Over.mk (𝟙 _))
  let b : fM.hom.hom.obj ZR ⟶ q'.y.hom.obj (Over.mk (𝟙 _)) :=
    Over.homMk (eqToHom hsrc ≫ e.specialOver ≫ eqToHom htgt.symm)
      (Over.mkIdTerminal.hom_ext _ _)
  have hb : Y.val.val.p.IsHomLift e.specialOver b :=
    IsHomLift.of_fac' _ _ _ hsrc htgt rfl
  refine nonempty_dottedArrow_of_span B q' e (cK ≫ n0) hn m hm b hb ?_
  have hc : e.genericOver ≫ q'.genericMap = e.genericMap ≫ e.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    simp only [Over.comp_left, Functor.map_comp]
    rw [e.genericMap_left, e.specialOver_left, e.genericOver_left, q'.genericMap_left,
      ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) e.fraction_comm.symm
  have hl : Y.val.val.p.IsHomLift (e.genericOver ≫ q'.genericMap)
      (fM.hom.hom.map (cK ≫ n0) ≫ pointLink B q') := by
    have := pointLink_lift B q'
    infer_instance
  have hr : Y.val.val.p.IsHomLift (e.genericOver ≫ q'.genericMap) (fM.hom.hom.map m ≫ b) := by
    rw [hc]
    infer_instance
  have : (Over.forget (Over.mk (𝟙 (B.obj hZ)))).Faithful := inferInstance
  apply (Over.forget (Over.mk (𝟙 (B.obj hZ)))).map_injective
  exact (IsHomLift.fac' Y.val.val.p (e.genericOver ≫ q'.genericMap) _).trans
    (IsHomLift.fac' Y.val.val.p (e.genericOver ≫ q'.genericMap) _).symm

/-- **The assembly of Stacks 0E9C, with the stable reduction theorem in place of the valuative
hypothesis.** As `AlgebraicGeometry.moduliStableCurves_isDeligneMumford_proper_smooth_of`, whose
input `hlift` (the hypothesis of Stacks 0CQM for `𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)`) is here proved from
`hred`, Stacks 0E98 (1) read in families of curves
(`AlgebraicGeometry.denseTestExistence_moduliSmoothCurves_of_stableReduction`). The other inputs
are the results the source cites, each an explicit hypothesis. -/
theorem moduliStableCurves_isDeligneMumford_proper_smooth_of_stableReduction (g : ℕ)
    (hP : IsOpenCurvesLocus B hZ (IsStableGenusCurveFamily B hZ g))
    (hQ : IsOpenCurvesLocus B hZ (IsSmoothGenusCurveFamily B hZ g))
    (hcurves : Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hDM : Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val.val)
    (hsmooth : IsSmoothOverIntegers B hZ h hP)
    (hopen : (curvesSmallOpenSubstack B hZ h hQ).pointSet ⊆
        (curvesSmallOpenSubstack B hZ h hP).pointSet ∧
      (curvesSmallOpenSubstack B hZ h hP).pointSet ⊆
        @closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
          (curvesSmallOpenSubstack B hZ h hQ).pointSet)
    (hsep : Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hqc : Stack.IsQuasiCompactStack.{u, w} B integerBase hZ
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.property)
    (hchow : ∀ (hT : B.Contains (⊤_ Scheme.{u}))
      {𝒳' : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
      {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B integerBase hZ Y),
      Space.IsQuasiCompactSpace B integerBase hZ Y →
      Space.IsAbsolutelyQuasiSeparated B integerBase hZ hT Y →
      ∀ (f' : 𝒳' ⟶ Stack.algebraicSpaceStack.{u, w} B integerBase hZ Y hY),
        Stack.AlgebraicStacks.IsSeparated B integerBase hZ f' →
        Stack.AlgebraicStacks.IsFiniteType B integerBase hZ f' →
        ∃ (X Xbar : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u)
          (hX : IsAlgebraicSpace B integerBase hZ X)
          (_ : IsAlgebraicSpace B integerBase hZ Xbar)
          (a : Stack.algebraicSpaceStack.{u, w} B integerBase hZ X hX ⟶ 𝒳')
          (i : X ⟶ Xbar) (g : Xbar ⟶ Y),
          Stack.AlgebraicStacks.IsProper B integerBase hZ a ∧
          Stack.IsSurjective B integerBase hZ a ∧
          Space.IsOpenImmersion B integerBase hZ i ∧ Space.IsProper B integerBase hZ g ∧
          Nonempty (a ≫ f' ≅
            Stack.algebraicSpaceStackMap.{u, w} B integerBase hZ hX hY (i ≫ g)))
    (hred : HasStableReductionCurveFamilies B hZ g) :
    Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val.val ∧
      Stack.AlgebraicStacks.IsProper B integerBase hZ
        ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
          Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      IsSmoothOverIntegers B hZ h hP ∧
      ∃ hle : (curvesSmallOpenSubstack B hZ h hQ).property ≤
          (curvesSmallOpenSubstack B hZ h hP).property,
        @Dense _ (Stack.pointTopology B integerBase hZ
            (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
          (Set.range (Stack.AlgebraicStacks.pointsMap B integerBase hZ
            (Stack.OpenSubstack.homOfLE B integerBase hZ (curvesSmallOpenSubstack B hZ h hQ)
              (curvesSmallOpenSubstack B hZ h hP) hle))) :=
  moduliStableCurves_isDeligneMumford_proper_smooth_of B hZ h g hP hQ hcurves hDM hsmooth hopen
    hsep hqc hchow (denseTestExistence_moduliSmoothCurves_of_stableReduction B hZ h g hP hQ _ hred)

end AlgebraicGeometry

end
