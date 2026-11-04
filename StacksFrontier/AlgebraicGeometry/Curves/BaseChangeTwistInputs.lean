module

public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingField
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.AlgebraicGeometry.NodalContraction.GenericFibreField
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import StacksFrontier.AlgebraicGeometry.Curves.JacobianCriterionNodal
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Curves.BaseChangeTwistLowCohomology

/-!
# The two geometric inputs of [Stacks, Tag 0B9Y]

[Stacks, Tag 0B9Y]
(`AlgebraicGeometry.exists_invertible_baseChangeTwist_finrank_cohomologyOverField_eq_one`)
is proved from two named inputs: `AlgebraicGeometry.AmpleTwistStart`, a twist `𝓛 ⊗ p^*𝓛₀` of a
given invertible module `𝓛` on `X_K` by an invertible module on `X` with vanishing `H¹` and a
nonzero section, and `AlgebraicGeometry.PointIdealTwistStep`, the twisting-down step by a
`k`-rational point. This file proves both for a smooth proper curve `X` over a separably closed
field `k`, so that Tag 0B9Y holds with no input.

## Main results

* `AlgebraicGeometry.ampleTwistStart_holds`: the start, with `𝓛₀` a high power of an ample module
  on `X`; its twist has large degree, hence vanishing `H¹` ([Stacks, Tag 0B5U]) and, by
  Riemann-Roch, a nonzero section.
* `AlgebraicGeometry.pointIdealTwistStep_holds`: the step, twisting down by a `k`-rational point
  of `X` above which a given section does not vanish.
* `AlgebraicGeometry.exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed`:
  **[Stacks, Tag 0B9Y]**, with no input.

## References

* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0B90](https://stacks.math.columbia.edu/tag/0B90)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- Precomposing the first map of a complex with a morphism keeps the composite zero. -/
theorem comp_comp_eq_zero {C : Type*} [Category C] [Preadditive C] {A A' B D : C}
    (e : A' ⟶ A) (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0) : (e ≫ f) ≫ g = 0 := by
  rw [Category.assoc, w, Limits.comp_zero]

/-- Precomposing the first map of a short exact sequence with an isomorphism keeps it short
exact. -/
theorem shortExact_mk_iso_comp {C : Type*} [Category C] [Preadditive C] {A A' B D : C}
    (e : A' ≅ A) (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    (ShortComplex.mk (e.hom ≫ f) g (by rw [Category.assoc, w, Limits.comp_zero])).ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := ShortComplex.mk f g w)
    (S₂ := ShortComplex.mk (e.hom ≫ f) g (by rw [Category.assoc, w, Limits.comp_zero]))
    e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)) h

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
private theorem isInvertible_pullback_of_isInvertible {X X' : Scheme.{u}} (p : X' ⟶ X)
    (N : X.Modules)
    (hN : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) N) :
    Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) ((Scheme.Modules.pullback p).obj N) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hN
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
    (Stacks.Divisors.pullback_isInvertible p N)

/-! ### Picard classes of the twists -/

section PicardClass

variable {X X' : Scheme.{u}}

/-- The Picard class of a twist `𝓛 ⊗ p^*𝓝` is `[𝓛] + p^*[𝓝]`. -/
theorem picardClass_baseChangeTwist (p : X' ⟶ X) (L : X'.Modules) (N : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) L)
    (hN : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) N)
    (hLN : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) (baseChangeTwist p L N)) :
    Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) (baseChangeTwist p L N) hLN =
      Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
          (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) L hL +
        Stacks.Picard.schemePullbackClass p
          (Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
            (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) N hN) := by
  have hpN := Stacks.RingedSpace.modulePullback_isInvertible_of p.toLRSHom.toShHom N hN
  have hpN' := isInvertible_pullback_of_isInvertible p N hN
  have e : Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) ((Scheme.Modules.pullback p).obj N)
        hpN' =
      Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace)
        ((Stacks.RingedSpace.pullbackFunctor p.toLRSHom.toShHom).obj N) hpN :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨(Stacks.ProjectiveBundleQuotients.pullbackIso p).app N⟩
  show _ = _ + Stacks.Picard.pullbackClass p.toLRSHom.toShHom _
  rw [Stacks.Picard.pullbackClass_classOf p.toLRSHom.toShHom N hN, ← e]
  exact (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ L _ hL hpN' hLN).symm

/-- **The pullback of the class of `𝒪(D)` is the class of `𝒪` of the inverse image**
([Stacks, Tag 0C4U]), when the inverse image is an effective Cartier divisor. -/
theorem schemePullbackClass_divisorPicardClass (p : X' ⟶ X) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsPullbackDefined p D] :
    Stacks.Picard.schemePullbackClass p (Stacks.Divisors.picardClass D) =
      Stacks.Divisors.picardClass (D.comap p) :=
  (Stacks.Picard.pullbackClass_classOf p.toLRSHom.toShHom (Stacks.Divisors.invertibleSheaf' D)
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)).trans
    ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨((Stacks.ProjectiveBundleQuotients.pullbackIso p).app _).symm ≪≫
        Stacks.Divisors.invertibleSheafPullbackIso p D⟩)

end PicardClass

/-- **The twist by `𝓛₀ ⊗ 𝓘_C` is the ideal twist of the twist by `𝓛₀`.** For an effective Cartier
divisor `C` on `X` whose inverse image in `X'` is one, there is an invertible `𝓛₁` on `X` with
`𝓛 ⊗ p^*𝓛₁ ≅ 𝓘_{p^{-1}C} ⊗ (𝓛 ⊗ p^*𝓛₀)`: the two sides have the same Picard class. -/
theorem exists_baseChangeTwist_iso_idealTwist {X X' : Scheme.{u}} (p : X' ⟶ X) (L : X'.Modules)
    (L₀ : X.Modules) (C : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor C]
    [Stacks.Divisors.IsPullbackDefined p C] [hLi : Stacks.Ample.IsInvertibleModule X' L]
    [hL₀ : Stacks.Ample.IsInvertibleModule X L₀] :
    ∃ L₁ : X.Modules, Stacks.Ample.IsInvertibleModule X L₁ ∧
      Nonempty (baseChangeTwist p L L₁ ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj
          (baseChangeTwist p L L₀)).obj (Stacks.Divisors.idealSheafOfModules (C.comap p))) := by
  let M := baseChangeTwist p L L₀
  let C' := C.comap p
  have hC' : Stacks.Divisors.IsEffectiveCartierDivisor C' :=
    ‹Stacks.Divisors.IsPullbackDefined p C›
  have hLs : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) L := hLi
  have hL₀s : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L₀ := hL₀
  let x₁ : Stacks.Picard.ofScheme X :=
    Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L₀ hL₀s +
      Stacks.Divisors.negativeTwistPicardClass C
  let L₁ := (Stacks.Picard.picardRepresentative X.toRingedSpace x₁).obj
  have hL₁ : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L₁ :=
    (Stacks.Picard.picardRepresentative X.toRingedSpace x₁).property
  refine ⟨L₁, hL₁, ?_⟩
  have hI' : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace)
      (Stacks.Divisors.idealSheafOfModules C') := hC'
  have : Stacks.SheafOfModules.IsInvertible
      ((sheafToPresheaf (Opens.grothendieckTopology X') CommRingCat).obj X'.sheaf)
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X') L := hLi
  have hpL₀ := isInvertible_pullback_of_isInvertible p L₀ hL₀s
  have hpL₁ := isInvertible_pullback_of_isInvertible p L₁ hL₁
  have hMs : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) M :=
    @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ _ _ _ _ L _ hLs hpL₀
  have hB : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) (baseChangeTwist p L L₁) :=
    @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ _ _ _ _ L _ hLs hpL₁
  have := hI'
  have := hMs
  have hIM : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj M).obj
        (Stacks.Divisors.idealSheafOfModules C')) :=
    Stacks.SheafOfModules.tensorProduct_isInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property (Stacks.Divisors.idealSheafOfModules C') M
  have hIM' : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj M).obj
        (Stacks.Divisors.idealSheafOfModules C')) := hIM
  have h1 := picardClass_baseChangeTwist p L L₁ hLs hL₁ hB
  have h3 := picardClass_baseChangeTwist p L L₀ hLs hL₀s hMs
  have h2 := Stacks.SheafOfModules.picardClass_tensorSheaf X'.toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) (Stacks.Divisors.idealSheafOfModules C')
    M hI' hMs hIM'
  have hx₁ : Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L₁ hL₁ = x₁ :=
    Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x₁
  have hneg : Stacks.Picard.schemePullbackClass p (Stacks.Divisors.negativeTwistPicardClass C) =
      Stacks.Divisors.negativeTwistPicardClass C' := by
    rw [Stacks.Divisors.negativeTwistPicardClass_eq_neg,
      Stacks.Divisors.negativeTwistPicardClass_eq_neg,
      show Stacks.Picard.schemePullbackClass p (-Stacks.Divisors.picardClass C) =
        -Stacks.Picard.schemePullbackClass p (Stacks.Divisors.picardClass C) from
        map_neg (Stacks.Picard.schemePullbackClassHom p) _,
      schemePullbackClass_divisorPicardClass]
  have hI : Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace)
      (Stacks.Divisors.idealSheafOfModules C') hI' =
      Stacks.Divisors.negativeTwistPicardClass C' := rfl
  have hcls : Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) (baseChangeTwist p L L₁) hB =
      Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj M).obj
          (Stacks.Divisors.idealSheafOfModules C')) hIM' := by
    refine h1.trans (Eq.trans ?_ h2)
    rw [hx₁, h3, hI, ← hneg, Stacks.Picard.schemePullbackClass_add]
    abel
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hcls

section BaseChange

variable (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X)
  (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [IsCurve k f] [Smooth f] [IsProper f]

include hp

omit [Field K] [Algebra k K] hp [IsProper f] in
/-- A smooth curve over a separably closed field is geometrically integral. -/
theorem geometricallyIntegral_of_isCurve_of_isSepClosed : GeometricallyIntegral f :=
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

omit [IsSepClosed k] [IsCurve k f] [Smooth f] in
/-- The base change of the curve is proper. -/
theorem isProper_baseChange : IsProper f' := MorphismProperty.of_isPullback hp ‹_›

omit [IsProper f] in
/-- The base change of the curve is geometrically integral. -/
theorem geometricallyIntegral_baseChange : GeometricallyIntegral f' :=
  have := geometricallyIntegral_of_isCurve_of_isSepClosed k f
  MorphismProperty.of_isPullback hp this

/-- The base change of the curve is a curve. -/
theorem isCurve_baseChange : IsCurve K f' := by
  have := isProper_baseChange k K f f' p hp
  have := geometricallyIntegral_baseChange k K f f' p hp
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_subsingleton f'
  refine isCurve_of_topologicalKrullDim_eq_one K f' ?_
  rw [topologicalKrullDim_baseChange k K p f' f hp]
  exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)

/-- **The start of the induction of [Stacks, Tag 0B9Y]** (`AlgebraicGeometry.AmpleTwistStart`).
For a smooth proper curve `X` over a separably closed field `k`, a field extension `K/k` and an
invertible module `𝓛` on `X_K`, a high power `𝓛₀ = A^{⊗ d}` of an ample module `A` on `X`
twists `𝓛` to a module with vanishing `H¹` and a nonzero section: the twist has degree
`deg 𝓛 + d · deg A`, which is at least `2g - 1` and `g` once `d` is large, since `A` pulls back to
an ample module on `X_K` and so has positive degree there ([Stacks, Tags 0B90 and 0B5U]). -/
theorem ampleTwistStart_holds (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] :
    AmpleTwistStart K f' p L := by
  -- the geometry of `X` and `X_K`
  have hdimX : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)
  have : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  have : IsProper f' := isProper_baseChange k K f f' p hp
  have : GeometricallyIntegral f' := geometricallyIntegral_baseChange k K f f' p hp
  have : IsCurve K f' := isCurve_baseChange k K f f' p hp
  have hdim' : topologicalKrullDim X' = 1 := IsCurve.topologicalKrullDim_eq_one (k := K) (f := f')
  have : IsAffineHom p := MorphismProperty.of_isPullback hp.flip inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian f'
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop) :=
    isIso_globalSections_of_geometricallyIntegral K f'
  -- an ample module on `X`, and its pullback to `X_K`
  obtain ⟨A, hAinv, hAamp⟩ := Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X hdimX
  have := hAinv
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A :=
    hAinv
  have hA'inv : AlgebraicGeometry.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property ((Scheme.Modules.pullback p).obj A) :=
    Stacks.Divisors.pullback_isInvertible p A
  have hA'amp := Scheme.Modules.isAmple_pullback_of_isAffineHom p A hAamp
  have : Stacks.Ample.IsInvertibleModule X' ((Scheme.Modules.pullback p).obj A) := hA'inv
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L :=
    ‹Stacks.Ample.IsInvertibleModule X' L›
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X' L
  -- Serre vanishing for the twists of `𝓛`
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
      f' L ((Scheme.Modules.pullback p).obj A)
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X' _ hA'amp)
  -- the exponent
  have hpos := invertibleCurveDegree_pos_of_isAmple_of_isCurve K f' hdim'.le
    ((Scheme.Modules.pullback p).obj A) hA'amp
  set d : ℕ := max d₀ (Int.toNat ((genus f' : ℤ) - invertibleCurveDegree K f' hdim'.le L)) with hd
  -- the twist, in the spelling of the degree computations
  let T := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.toRingedSpace.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ (X'.toRingedSpace.presheaf) (forget₂ CommRingCat RingCat)
      ((structureSheafRing X'.toRingedSpace).property)⟩).obj L).obj
    (Stacks.SheafOfModules.Invertible.tensorPower X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property ((Scheme.Modules.pullback p).obj A) d))
  let e₁ : baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ)) ≅ T :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj L).mapIso
      (Scheme.Modules.pullbackTensorPowerIso p A d)
  let e₂ : T ≅ Stacks.RelativeVeryAmple.tensorModules X' L
      (Stacks.Ample.tensorPowModule X' ((Scheme.Modules.pullback p).obj A) (d : ℤ)) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj L).mapIso
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X' _ (d : ℤ))
  have hP : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (Stacks.SheafOfModules.Invertible.tensorPower X'.toRingedSpace.presheaf
        (structureSheafRing X'.toRingedSpace).property ((Scheme.Modules.pullback p).obj A) d) :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property ((Scheme.Modules.pullback p).obj A) d
  have : Stacks.SheafOfModules.IsInvertible
      ((sheafToPresheaf (Opens.grothendieckTopology X') CommRingCat).obj X'.sheaf)
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X') L :=
    ‹Stacks.Ample.IsInvertibleModule X' L›
  have : Stacks.SheafOfModules.IsInvertible
      ((sheafToPresheaf (Opens.grothendieckTopology X') CommRingCat).obj X'.sheaf)
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X')
      (Stacks.SheafOfModules.Invertible.tensorPower X'.toRingedSpace.presheaf
        (structureSheafRing X'.toRingedSpace).property ((Scheme.Modules.pullback p).obj A) d) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr hP
  have hpB := isInvertible_pullback_of_isInvertible p
    (Scheme.Modules.tensorPowerModules A (d : ℤ))
    ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      (Scheme.Modules.algebraicGeometryIsInvertible_tensorPowerModules A (d : ℤ)))
  have hT : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 T :=
    Stacks.SheafOfModules.tensorProduct_isInvertible _ _ L _
  have hB : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) :=
    @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ _ _ _ _ L _ ‹_› hpB
  -- its degree
  have hdegT : invertibleCurveDegree K f' hdim'.le T =
      invertibleCurveDegree K f' hdim'.le L +
        d * invertibleCurveDegree K f' hdim'.le ((Scheme.Modules.pullback p).obj A) := by
    rw [invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one K f' hdim'.le L _
      hLinv hP hT, invertibleCurveDegree_tensorPower_eq_mul_of_isCurve K f' hdim'.le _ (d : ℤ)]
  have hdegB : invertibleCurveDegree K f' hdim'.le
      (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) =
      invertibleCurveDegree K f' hdim'.le T := invertibleCurveDegree_eq_of_iso K f' hdim'.le e₁
  -- `H¹` vanishes
  have hvan : IsZero (cohomologyOverField K f'
      (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) 1) :=
    ((isZero_cohomologyOverField_iff_isZero_hgroup K f' _ 1).mpr
      (hd₀ d 1 (le_max_left _ _) Nat.one_pos)).of_iso (cohomologyOverFieldIso K f' (e₁ ≪≫ e₂) 1)
  -- `H⁰` is finite dimensional of positive dimension
  have : (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X' _
  have hfd := finiteDimensional_cohomologyOverField_of_isProper K f'
    (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) 0
  have hrr := finrank_cohomologyOverField_zero_sub_one_eq K f' hdim'.le
    (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) hB
  have h1 : Module.finrank K (cohomologyOverField K f'
      (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) 1) = 0 := by
    have := ModuleCat.subsingleton_of_isZero hvan
    exact Module.finrank_zero_of_subsingleton
  rw [finrank_cohomologyOverField_unit_zero_eq_one f', h1] at hrr
  change _ = @invertibleCurveDegree K _ X' f' _ hdim'.le _ hB + _ - _ at hrr
  rw [hdegB, hdegT] at hrr
  have hd1 : ((genus f' : ℤ) - invertibleCurveDegree K f' hdim'.le L) ≤ d := by
    have := Int.self_le_toNat ((genus f' : ℤ) - invertibleCurveDegree K f' hdim'.le L)
    omega
  have hd2 : (d : ℤ) ≤ d * invertibleCurveDegree K f' hdim'.le
      ((Scheme.Modules.pullback p).obj A) := by nlinarith
  have hpos0 : 0 < Module.finrank K (cohomologyOverField K f'
      (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) 0) := by omega
  refine ⟨Scheme.Modules.tensorPowerModules A (d : ℤ),
    Module.finrank K (cohomologyOverField K f'
      (baseChangeTwist p L (Scheme.Modules.tensorPowerModules A (d : ℤ))) 0) - 1,
    Scheme.Modules.algebraicGeometryIsInvertible_tensorPowerModules A (d : ℤ), hvan, hfd, ?_⟩
  omega

omit [IsProper f] in
/-- **A rational point of `X` below a nonempty open of `X_K`.** Every nonempty open `V ⊆ X_K`
contains a point above a closed point `x₀` of `X` whose residue field is `k`: the projection
`X_K ⟶ X` is open, being a base change of `Spec K ⟶ Spec k`, and the closed points of `X` with
finite separable residue field are dense ([Stacks, Tag 056U]); over the separably closed `k` such
a residue field is `k`. -/
@[sga "3 VIA 2.5.4" "special case"]
theorem exists_rationalPoint_mem (V : Set X') (hVo : IsOpen V) (hVne : V.Nonempty) :
    ∃ (x₀ : X) (hx₀ : IsClosed ({x₀} : Set X)), IsIso (X.fromSpecResidueField x₀ ≫ f) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x₀}, hx₀⟩ : TopologicalSpace.Closeds X)) ∧
      ∃ v ∈ V, p.base v = x₀ := by
  have : UniversallyOpen p := MorphismProperty.of_isPullback hp.flip inferInstance
  have hUo : IsOpen (p.base '' V) := p.isOpenMap V hVo
  obtain ⟨x₀, ⟨v, hv, rfl⟩, hcl, hfin, hsep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth f).inter_open_nonempty _
      hUo (hVne.image _)
  let φ : CommRingCat.of k ⟶ X.residueField (p.base v) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (p.base v)
  let : Algebra k (X.residueField (p.base v)) := φ.hom.toAlgebra
  have hbij : Function.Bijective φ :=
    ⟨φ.hom.injective, IsSepClosed.algebraMap_surjective k (X.residueField (p.base v))⟩
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr hbij
  have hφ : Spec.map φ = X.fromSpecResidueField (p.base v) ≫ f := by
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecResidueField_toSpecΓ, Category.assoc,
      Category.assoc, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hsepx : Algebra.IsSeparableExtension k (X.residueField (p.base v)) :=
    Stacks.Curves.isSeparableExtension_of_surjective_algebraMap hbij.2
  have h := smoothAt_closedPoint_tfae_of_isCurve_of_isSeparable k f hcl hsepx
  refine ⟨p.base v, hcl, ?_, (h (InfinitesimalLifting.SmoothAt f (p.base v)) (by simp)
    (Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{p.base v}, hcl⟩ : TopologicalSpace.Closeds X)))
      (by simp)).mp (InfinitesimalLifting.smoothAt_of_smooth f _), v, hv, rfl⟩
  rw [← hφ]
  infer_instance

omit [IsSepClosed k] [IsCurve k f] [Smooth f] [IsProper f] in
/-- **The inverse image in `X_K` of a rational point of `X` is a copy of `Spec K`.** If `x₀` is a
closed point of `X` with `Spec κ(x₀) ⟶ Spec k` an isomorphism, the closed subscheme of `X_K` cut
out by the inverse image of the reduced point `x₀` maps isomorphically to `Spec K`. -/
theorem isIso_comap_subschemeι_comp (x₀ : X) (hx₀ : IsClosed ({x₀} : Set X))
    (hiso : IsIso (X.fromSpecResidueField x₀ ≫ f)) :
    IsIso (((X.fromSpecResidueField x₀).ker.comap p).subschemeι ≫ f') := by
  have : IsClosedImmersion (X.fromSpecResidueField x₀) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx₀
  let C := (X.fromSpecResidueField x₀).ker
  have h1 : IsIso (C.subschemeι ≫ f) := by
    have e : C.subschemeι = inv (X.fromSpecResidueField x₀).toImage ≫ X.fromSpecResidueField x₀ :=
      by rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
    rw [e, Category.assoc]
    infer_instance
  have sq := (IsPullback.of_hasPullback p C.subschemeι).flip.paste_vert hp
  have : IsIso (pullback.fst p C.subschemeι ≫ f') := sq.isIso_snd_of_isIso h1
  rw [← C.comapIso_hom_fst p, Category.assoc]
  infer_instance

omit [IsSepClosed k] [IsCurve k f] [Smooth f] [IsProper f] in
/-- **The sections of an invertible module on the inverse image of a rational point** form a
one-dimensional `K`-vector space: that inverse image is `Spec K`, on which an invertible module is
trivial. This is the clause of `AlgebraicGeometry.PointIdealTwistStep` that records the
`k`-rationality of the point. -/
theorem finrank_cohomologyOverField_pullback_comap_eq_one (x₀ : X) (hx₀ : IsClosed ({x₀} : Set X))
    (hiso : IsIso (X.fromSpecResidueField x₀ ≫ f)) (M : X'.Modules)
    [hM : Stacks.Ample.IsInvertibleModule X' M] :
    Module.finrank K (cohomologyOverField K
      (((X.fromSpecResidueField x₀).ker.comap p).subschemeι ≫ f')
      ((Scheme.Modules.pullback ((X.fromSpecResidueField x₀).ker.comap p).subschemeι).obj M) 0)
      = 1 := by
  set D := (X.fromSpecResidueField x₀).ker.comap p with hD
  have hg := isIso_comap_subschemeι_comp k K f f' p hp x₀ hx₀ hiso
  have hsub : Subsingleton (D.subscheme : Type u) := by
    constructor
    intro z z'
    have hinj : Function.Injective (D.subschemeι ≫ f').base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (D.subschemeι ≫ f')))).injective
    exact hinj (Subsingleton.elim _ _)
  have hpb : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      (structureSheafRing D.subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback D.subschemeι).obj M) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback D.subschemeι M hM
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology D.subscheme
    ((Scheme.Modules.pullback D.subschemeι).obj M)
  have e' : (Scheme.Modules.pullback D.subschemeι).obj M ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf := e
  rw [finrank_cohomologyOverField_eq_of_iso K (D.subschemeι ≫ f') e' 0]
  have : IsIso (Scheme.Hom.appTop (D.subschemeι ≫ f')) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (D.subschemeι ≫ f') ⊤))
  exact finrank_cohomologyOverField_unit_zero_eq_one (D.subschemeι ≫ f')

/-- **The geometric step of the induction of [Stacks, Tag 0B9Y]**
(`AlgebraicGeometry.PointIdealTwistStep`). Given a twist `𝓜 = 𝓛 ⊗ p^*𝓛₀` with a nonzero section
`s`, choose a `k`-rational point `x₀` of `X` above which `s` does not vanish (Tag 056U) and let
`𝓛₁ = 𝓛₀ ⊗ 𝓘_{x₀}`, the ideal sheaf of `x₀` being invertible (Tag 0B8Y). Its twist is
`𝓘_{x₀,K} ⊗ 𝓜`, whose quotient of `𝓜` is `i_*i^*𝓜` for `i` the inclusion of the inverse image
`x₀,K ≅ Spec K` of `x₀`; there `H⁰` is one-dimensional, and `s` does not vanish. -/
theorem pointIdealTwistStep_holds (L : X'.Modules) [hLi : Stacks.Ample.IsInvertibleModule X' L] :
    PointIdealTwistStep K f' p L := by
  intro L₀ t hL₀ h
  have : IsProper f' := isProper_baseChange k K f f' p hp
  have : GeometricallyIntegral f' := geometricallyIntegral_baseChange k K f f' p hp
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_subsingleton f'
  have : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  let M := baseChangeTwist p L L₀
  have hpL₀ := isInvertible_pullback_of_isInvertible p L₀ hL₀
  have hMs : Stacks.Ample.IsInvertibleModule X' M :=
    @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ _ _ _ _ L _ hLi hpL₀
  have hMa : AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj
      X'.ringCatSheaf.property M :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hMs
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 M := hMa
  have hpos : 0 < Module.finrank K (cohomologyOverField K f' M 0) := by
    rw [h.finrank_zero]; omega
  have _ := FiniteDimensional.of_finrank_pos hpos
  have _ : Nontrivial (cohomologyOverField K f' M 0 : Type u) := Module.finrank_pos_iff.mp hpos
  have _ : Nontrivial Γ(M, ⊤) := (cohomologyOverFieldZeroEquivSections K f' M).symm.nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(M, ⊤))
  have hLr : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property M := hMs
  have hbridge : Stacks.SheafOfModules.nonvanishingLocus (X := X'.toRingedSpace) M
      (Stacks.SheafOfModules.sectionsOfTop M s) = Stacks.Ample.nonvanishingLocus M s :=
    nonvanishingLocus_sectionsOfTop_eq M s
  have hVo : IsOpen (Stacks.Ample.nonvanishingLocus M s) := by
    rw [← hbridge]
    exact Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := X'.toRingedSpace) M _
  have hVne : (Stacks.Ample.nonvanishingLocus M s).Nonempty :=
    hbridge ▸ nonempty_nonvanishingLocus_of_ne_zero M s hs
  obtain ⟨x₀, hx₀, hiso, hCeff, v, hv, hvx⟩ := exists_rationalPoint_mem k K f f' p hp _ hVo hVne
  have : IsClosedImmersion (X.fromSpecResidueField x₀) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx₀
  let C := (X.fromSpecResidueField x₀).ker
  have hC : Stacks.Divisors.IsEffectiveCartierDivisor (X.fromSpecResidueField x₀).ker := by
    rwa [ker_fromSpecResidueField X x₀ hx₀]
  have : Stacks.Divisors.IsPullbackDefined p C := Stacks.Divisors.isPullbackDefined_of_flat p C hC
  let C' := C.comap p
  have hC' : Stacks.Divisors.IsEffectiveCartierDivisor C' :=
    ‹Stacks.Divisors.IsPullbackDefined p C›
  have hMa' : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X'.sheaf).property M := hMa
  obtain ⟨w, hSE⟩ := Stacks.Divisors.exists_shortExact_invertibleTwist C' M hMa'
  obtain ⟨L₁, hL₁, ⟨E⟩⟩ := exists_baseChangeTwist_iso_idealTwist p L L₀ C
  obtain ⟨z, hzv⟩ : v ∈ Set.range C'.subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    show p.base v ∈ (C.support : Set X)
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx₀.closure_eq, hvx]
    rfl
  refine ⟨C'.subscheme, C'.subschemeι, inferInstance, L₁,
    E.hom ≫ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj M).map
      (Stacks.Divisors.idealInclusion C') ≫ (Stacks.Divisors.tensorUnitIso M).hom),
    (modulePullbackPushforwardAdjunction C'.subschemeι.toLRSHom.toShHom).unit.app M, ?_, ?_,
    hL₁,
    finrank_cohomologyOverField_pullback_comap_eq_one k K f f' p hp x₀ hx₀ hiso M,
    (cohomologyOverFieldZeroEquivSections K f' M).symm s, ?_⟩
  · exact comp_comp_eq_zero E.hom _ _ w
  · exact shortExact_mk_iso_comp E _ _ w hSE
  · intro hc
    refine app_top_unit_ne_zero_of_mem_nonvanishingLocus C'.subschemeι M s z (hzv ▸ hv) ?_
    have key := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap K f'
      ((modulePullbackPushforwardAdjunction C'.subschemeι.toLRSHom.toShHom).unit.app M)
      ((cohomologyOverFieldZeroEquivSections K f' M).symm s)
    exact ((congrArg (fun t => (Scheme.Modules.Hom.app
            ((modulePullbackPushforwardAdjunction C'.subschemeι.toLRSHom.toShHom).unit.app M) ⊤) t)
          (Equiv.apply_symm_apply (cohomologyOverFieldZeroEquivSections K f' M) s).symm).trans
        (key.symm.trans
          ((congrArg (cohomologyOverFieldZeroEquivSections K f'
              ((Scheme.Modules.pushforward C'.subschemeι).obj
                ((Scheme.Modules.pullback C'.subschemeι).obj M))) hc).trans
            (cohomologyOverFieldZeroEquivSections_zero K f' _))))

end BaseChange

end AlgebraicGeometry

end
