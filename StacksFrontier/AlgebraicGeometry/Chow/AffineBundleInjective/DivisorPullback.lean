module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.BundleCyclePullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrincipalDivisorComponents
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainBoundaryCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisorOrder
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwisePresentation

/-!
# Pulling back the divisor differential along an affine-space bundle

Let `(S, δ)` be the base situation of chapter 42 and `f : X ⟶ Y` an affine-space bundle of rank
`r` between schemes locally of finite type over `S`. Pulling Milnor K-chains back along `f`
(`Stacks.Chow.bundleChainPullback`) carries the class at a point `y` to the generic point `ξ` of
the fibre over `y`, along `κ(y) → κ(ξ)`. This file proves that this pullback commutes with the
divisor differential of Stacks 0GU3:

  `div_X (f^* a) = f^* (div_Y a)`

for a locally finite family `a` of degree-one Milnor K-classes at the points of `Y` of relative
dimension `k + 1`. In Milnor degree zero the pullback of chains is flat pullback of cycles, so
this is Stacks 02RR applied one summand of the differential at a time.

For a single summand, at a point `y` of relative dimension `k + 1` with a unit `u` of `κ(y)`,
write `W = closure {y}` and `W' = f^{-1}(W)`. The restriction `W' ⟶ W` is again an
affine-space bundle, so `W'` is integral, with generic point `ξ`. Flat pullback of the principal
divisor of `u` on `W` is, by the closed-immersion case of Stacks 02RG and by Stacks 02RR on the
integral schemes `W'` and `W`, the principal divisor on `W'` of the pulled-back rational
function, whose value at `ξ` is the image of `u` in `κ(ξ)`; and that is the summand of the
differential on `X` at `ξ`.

## Main results

* `Stacks.Chow.rationalFunctionsEquivResidueFieldOfGenericPoint_dominantFunctionFieldMap` — the
  value at the generic point of a rational function pulled back along a dominant morphism of
  integral closed subschemes is the image of its value along the residue field map.
* `Stacks.Chow.pointClosureOrd_milnorKTransport_of_isAffineSpaceBundle` — one summand of the
  divisor differential is compatible with pulling back along an affine-space bundle.
* `Stacks.Chow.pointwiseDivisorDifferential_bundleChainPullback` — the divisor differential
  commutes with pulling back along an affine-space bundle.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RR](https://stacks.math.columbia.edu/tag/02RR)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The residue of a stalk map, transported along an equality of the image point, is the residue
field map applied to the transported residue. -/
theorem residue_eqToHom_stalkMap {T V : Scheme.{u}} (q : T ⟶ V) (x : T) {z : V}
    (h : q.base x = z) (a : V.presheaf.stalk z) :
    T.residue x ((eqToHom (congrArg V.presheaf.stalk h.symm) ≫ q.stalkMap x).hom a) =
      q.residueFieldMap x ((V.residueFieldCongr h.symm).hom (V.residue z a)) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Scheme.residueFieldCongr_refl, Iso.refl_hom]
  exact (congrArg (fun m ↦ m.hom a) (Scheme.residue_residueFieldMap q x)).symm

/-- **Residue field maps around a commutative square.** For `q ≫ ιB = ιA ≫ f` and points
`a ↦ b` under `q`, going from `κ(ιB b)` to `κ(a)` through `κ(f (ιA a))` and through `κ(b)`
gives the same map. -/
theorem residueFieldMap_comp_residueFieldMap_of_comm {A B X Y : Scheme.{u}} (ιA : A ⟶ X)
    (ιB : B ⟶ Y) (f : X ⟶ Y)
    (q : A ⟶ B) (hq : q ≫ ιB = ιA ≫ f) (a : A) {b : B} (hab : q.base a = b)
    (hy : ιB.base b = f.base (ιA.base a)) (t : Y.residueField (ιB.base b)) :
    ιA.residueFieldMap a (f.residueFieldMap (ιA.base a) ((Y.residueFieldCongr hy).hom t)) =
      q.residueFieldMap a ((B.residueFieldCongr hab.symm).hom (ιB.residueFieldMap b t)) := by
  subst hab
  have key : (Y.residueFieldCongr hy).hom ≫ f.residueFieldMap (ιA.base a) ≫
      ιA.residueFieldMap a = ιB.residueFieldMap (q.base a) ≫ q.residueFieldMap a := by
    have h1 : f.residueFieldMap (ιA.base a) ≫ ιA.residueFieldMap a =
        (ιA ≫ f).residueFieldMap a := (Scheme.residueFieldMap_comp ιA f a).symm
    have h2 := Scheme.residueFieldMap_comp q ιB a
    have h3 := Scheme.Hom.residueFieldMap_congr hq.symm a
    refine ((congrArg (fun m ↦ (Y.residueFieldCongr hy).hom ≫ m) h1).trans
      ((congrArg (fun m ↦ (Y.residueFieldCongr hy).hom ≫ m) h3).trans ?_))
    have hc : ∀ {z : Y} (e₁ : ιB.base (q.base a) = z) (e₂ : z = ιB.base (q.base a))
        (M : Y.residueField (ιB.base (q.base a)) ⟶ A.residueField a),
        (Y.residueFieldCongr e₁).hom ≫ (Y.residueFieldCongr e₂).hom ≫ M = M := by
      intro z e₁ e₂ M
      subst e₁
      simp
    rw [h2]
    exact hc hy _ _
  have := congrArg (fun m ↦ m.hom t) key
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.residueFieldCongr_refl,
    Iso.refl_hom, CommRingCat.hom_id, RingHom.id_apply] using this

/-- The value at the generic point `x` of a rational function on an integral closed subscheme
`V`, read back in the residue field of `V` at its generic point, is the residue of the
function there. -/
theorem residueFieldMap_rationalFunctionsEquivResidueFieldOfGenericPoint {X : Scheme.{u}}
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme) {x : X} (hx : genericPointOf V hV = x)
    (g : rationalFunctions V.subscheme) :
    V.subschemeι.residueFieldMap (genericPoint V.subscheme)
        ((X.residueFieldCongr hx.symm).hom
          (rationalFunctionsEquivResidueFieldOfGenericPoint V hV hx g)) =
      V.subscheme.residue (genericPoint V.subscheme)
        ((rationalFunctionsEquivFunctionField V.subscheme).1 g) := by
  subst hx
  exact (RingEquiv.ofBijective (V.subschemeι.residueFieldMap (genericPoint V.subscheme)).hom
    (bijective_residueFieldMap_of_isClosedImmersion V.subschemeι _)).apply_symm_apply
      ((rationalFunctionsEquivResidueField V.subscheme).1 g)

/-- The function-field map of a dominant morphism of integral schemes, followed by the residue at
the generic point, is the residue field map at the generic point. -/
theorem residue_dominantFunctionFieldMap {T V : Scheme.{u}} [IsIntegral T] [IsIntegral V]
    (q : T ⟶ V) [IsDominant q] (hgen : q.base (genericPoint T) = genericPoint V)
    (a : V.functionField) :
    T.residue (genericPoint T) (dominantFunctionFieldMap q a) =
      q.residueFieldMap (genericPoint T)
        ((V.residueFieldCongr hgen.symm).hom (V.residue (genericPoint V) a)) := by
  have hfield : dominantFunctionFieldMap q =
      (eqToHom (congrArg V.presheaf.stalk hgen.symm) ≫ q.stalkMap (genericPoint T)).hom := by
    rw [dominantFunctionFieldMap, stalkMap_eqToHom_eq_cast q (genericPoint T) _ hgen]
  rw [hfield]
  exact residue_eqToHom_stalkMap q (genericPoint T) hgen a

/-- **Values at generic points along a dominant morphism of integral closed subschemes.** Let
`q : V ⟶ W` be a dominant morphism of integral closed subschemes of `X` and `Y` lying over
`f : X ⟶ Y`, with generic points `x` and `f x`. The value at `x` of the pullback along `q` of a
rational function on `W` is the image, under `κ(f x) → κ(x)`, of its value at `f x`. -/
theorem rationalFunctionsEquivResidueFieldOfGenericPoint_dominantFunctionFieldMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.IdealSheafData) (W : Y.IdealSheafData)
    [hV : IsIntegral V.subscheme] [hW : IsIntegral W.subscheme] (q : V.subscheme ⟶ W.subscheme)
    [IsDominant q] (hq : q ≫ W.subschemeι = V.subschemeι ≫ f) {x : X}
    (hx : genericPointOf V hV = x) (hy : genericPointOf W hW = f.base x)
    (g : rationalFunctions W.subscheme) :
    rationalFunctionsEquivResidueFieldOfGenericPoint V hV hx
        ((rationalFunctionsEquivFunctionField V.subscheme).1.symm
          (dominantFunctionFieldMap q ((rationalFunctionsEquivFunctionField W.subscheme).1 g))) =
      f.residueFieldMap x (rationalFunctionsEquivResidueFieldOfGenericPoint W hW hy g) := by
  subst hx
  have hgen : q.base (genericPoint V.subscheme) = genericPoint W.subscheme :=
    ((tfae_isDominant_of_isIntegral q).out 1 2).mp (inferInstance : IsDominant q)
  apply (V.subschemeι.residueFieldMap (genericPoint V.subscheme)).hom.injective
  have hL := residueFieldMap_rationalFunctionsEquivResidueFieldOfGenericPoint V hV rfl
    ((rationalFunctionsEquivFunctionField V.subscheme).1.symm
      (dominantFunctionFieldMap q ((rationalFunctionsEquivFunctionField W.subscheme).1 g)))
  rw [Scheme.residueFieldCongr_refl, RingEquiv.apply_symm_apply] at hL
  have hR := residueFieldMap_rationalFunctionsEquivResidueFieldOfGenericPoint W hW hy g
  have hsq := residueFieldMap_comp_residueFieldMap_of_comm V.subschemeι W.subschemeι f q hq
    (genericPoint V.subscheme) hgen hy ((Y.residueFieldCongr hy.symm).hom
      (rationalFunctionsEquivResidueFieldOfGenericPoint W hW hy g))
  rw [hR] at hsq
  have hc : (Y.residueFieldCongr hy).hom ((Y.residueFieldCongr hy.symm).hom
      (rationalFunctionsEquivResidueFieldOfGenericPoint W hW hy g)) =
        rationalFunctionsEquivResidueFieldOfGenericPoint W hW hy g :=
    (Y.residueFieldCongr hy.symm).hom_inv_id_apply _
  refine hL.trans ((residue_dominantFunctionFieldMap q hgen _).trans (hsq.symm.trans ?_))
  exact congrArg (fun v ↦ V.subschemeι.residueFieldMap (genericPoint V.subscheme)
    (f.residueFieldMap (genericPointOf V hV) v)) hc

section Bundle

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) {r : ℕ}
  (hb : IsAffineSpaceBundle f r)

include hbase hb in
/-- **The inverse image of the closure of a point under an affine-space bundle has the generic
point of the fibre as its generic point.** A point `ξ` with `δ(ξ) = δ(f ξ) + r` specializes to
every point of its fibre, and the generic point of `f^{-1}(closure {f ξ})` lies over `f ξ` and
specializes to `ξ`. -/
theorem genericPointOf_comap_integralComponentAt_of_isAffineSpaceBundle {ξ : X}
    (hξ : relativeDimension C.dimensionFunction sX ξ =
      relativeDimension C.dimensionFunction sY (f.base ξ) + r)
    (hW : IsIntegral ((integralComponentAt (f.base ξ)).comap f).subscheme) :
    genericPointOf _ hW = ξ := by
  set W := integralComponentAt (f.base ξ) with hWdef
  have hrange : ∀ p, p ∈ Set.range (W.comap f).subschemeι.base ↔
      f.base p ∈ closure {f.base ξ} := fun p ↦ by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap, Set.mem_preimage,
      hWdef, coe_support_integralComponentAt]
  obtain ⟨z, hz⟩ := (hrange ξ).2 (subset_closure rfl)
  show (W.comap f).subschemeι.base (genericPoint (W.comap f).subscheme) = ξ
  set g := (W.comap f).subschemeι.base (genericPoint (W.comap f).subscheme) with hg
  have hgξ : g ⤳ ξ := by
    rw [← hz]
    exact (genericPoint_specializes z).map (W.comap f).subschemeι.continuous
  have hfg : f.base g = f.base ξ :=
    ((hgξ.map f.continuous).antisymm
      (specializes_iff_mem_closure.mpr ((hrange g).1 ⟨_, rfl⟩))).eq
  have hξg : ξ ⤳ g :=
    specializes_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb hξ hfg
  exact (hgξ.antisymm hξg).eq

include hbase hb in
/-- **One summand of the divisor differential pulls back along an affine-space bundle** (Stacks
02RR). Let `ξ` be the generic point of the fibre over a point `f ξ` of relative dimension
`k + 1`, and `u` a degree-one Milnor K-class at `f ξ`. The coefficient at `w` of the principal
divisor on `closure {ξ}` of the image of `u` in `κ(ξ)` is the coefficient at `f w` of the
principal divisor on `closure {f ξ}` of `u`, times the flat pullback multiplicity at `w`. -/
theorem pointClosureOrd_milnorKTransport_of_isAffineSpaceBundle [LocallyOfFiniteType f] [Flat f]
    (hf : AlgebraicGeometry.RelativeDimension f r) {k : ℤ} {ξ : X}
    (hξ : relativeDimension C.dimensionFunction sX ξ =
      relativeDimension C.dimensionFunction sY (f.base ξ) + r)
    (hk : relativeDimension C.dimensionFunction sY (f.base ξ) = k + 1)
    (u : MilnorKTheory (Y.residueField (f.base ξ)) 1) (w : X) :
    pointClosureOrd C sX ξ (milnorKTransport (f.residueFieldMap ξ).hom 1 u) w =
      pointClosureOrd C sY (f.base ξ) u (f.base w) * flatPullbackWeight C sX f (k + r) w := by
  set W := integralComponentAt (f.base ξ) with hWdef
  have hWint : IsIntegral W.subscheme := isIntegral_integralComponentAt _
  have hW'int : IsIntegral (W.comap f).subscheme :=
    isIntegral_of_isAffineSpaceBundle (comapRestrict W f) r
      (isAffineSpaceBundle_comapRestrict f hb W)
  have := locallyOfFiniteType_comapRestrict W f
  have := flat_comapRestrict W f
  have : IsDominant (comapRestrict W f) := isDominant_of_flat _
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sY)
  have : IsLocallyNoetherian (W.comap f).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((W.comap f).subschemeι ≫ sX)
  have hqr := relativeDimension_comapRestrict W f hf
  have hbq := comapRestrict_comp_base C sX sY f hbase W
  have hDim : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) := by
    rw [hWdef, schemeDeltaDimension_integralComponentAt, hk]
  have hgen := genericPointOf_comap_integralComponentAt_of_isAffineSpaceBundle C sX sY f hbase hb
    hξ hW'int
  set gY := integralComponentFunction (f.base ξ)
    (Additive.toMul (milnorKTheoryOneAddEquiv _ u)) with hgY
  set gg := (rationalFunctionsEquivFunctionField W.subscheme).1
    (gY : rationalFunctions W.subscheme) with hggdef
  have hgg : gg ≠ 0 := rationalFunctionsEquivFunctionField_ne_zero _ gY
  set v := Additive.toMul (milnorKTheoryOneAddEquiv _
    (milnorKTransport (f.residueFieldMap ξ).hom 1 u)) with hv
  set g' := (rationalFunctionUnitsEquivOfGenericPoint (W.comap f) hW'int hgen).symm v with hg'def
  -- the pulled-back rational function
  have hg' : (rationalFunctionsEquivFunctionField (W.comap f).subscheme).1
      (g' : rationalFunctions (W.comap f).subscheme) =
        dominantFunctionFieldMap (comapRestrict W f) gg := by
    have hval := rationalFunctionsEquivResidueFieldOfGenericPoint_dominantFunctionFieldMap f
      (W.comap f) W (comapRestrict W f) (comapRestrict_subschemeι W f) hgen
      (genericPointOf_integralComponentAt _) (gY : rationalFunctions W.subscheme)
    have h1 : rationalFunctionsEquivResidueFieldOfGenericPoint (W.comap f) hW'int hgen
        (g' : rationalFunctions (W.comap f).subscheme) = (v : X.residueField ξ) :=
      congrArg Units.val ((rationalFunctionUnitsEquivOfGenericPoint _ _ hgen).apply_symm_apply v)
    have h2 : (v : X.residueField ξ) = f.residueFieldMap ξ
        ((Additive.toMul (milnorKTheoryOneAddEquiv _ u) : (Y.residueField (f.base ξ))ˣ) :
          Y.residueField (f.base ξ)) := by
      rw [hv, milnorKTheoryOneAddEquiv_milnorKTransport]
      rfl
    have h3 : rationalFunctionsEquivResidueFieldOfGenericPoint W hWint
        (genericPointOf_integralComponentAt _) (gY : rationalFunctions W.subscheme) =
          ((Additive.toMul (milnorKTheoryOneAddEquiv _ u) : (Y.residueField (f.base ξ))ˣ) :
            Y.residueField (f.base ξ)) :=
      congrArg Units.val (integralComponentFunction_value _ _)
    have heq : (g' : rationalFunctions (W.comap f).subscheme) =
        (rationalFunctionsEquivFunctionField (W.comap f).subscheme).1.symm
          (dominantFunctionFieldMap (comapRestrict W f) gg) :=
      (rationalFunctionsEquivResidueFieldOfGenericPoint (W.comap f) hW'int hgen).injective
        (h1.trans (h2.trans ((congrArg _ h3).symm.trans hval.symm)))
    rw [heq, RingEquiv.apply_symm_apply]
  -- the left side is the divisor of `g'` on the inverse image
  have hL : pointClosureOrd C sX ξ (milnorKTransport (f.residueFieldMap ξ).hom 1 u) w =
      principalDivisorPushforward C sX (W.comap f) hW'int g' w := by
    rw [principalDivisorPushforward_eq_integralComponentAt C sX (W.comap f) hW'int hgen g',
      hg'def, MulEquiv.apply_symm_apply]
    rfl
  -- the right side is the flat pullback of the divisor of `gY`
  set γ : CycleGroup C (W.subschemeι ≫ sY) k := ⟨principalCycle W.subscheme gg, by
    simpa [show k + 1 - 1 = k by omega] using
      principalCycle_mem_cyclesOfDimension C (W.subschemeι ≫ sY) hDim gg⟩ with hγ
  have hR : pointClosureOrd C sY (f.base ξ) u (f.base w) * flatPullbackWeight C sX f (k + r) w =
      (flatPullback C sX sY f hbase r hf k
        (properPushforward C (W.subschemeι ≫ sY) sY W.subschemeι rfl k γ)).1 w := by
    rw [flatPullback_apply]
    rfl
  rw [hL, hR, flatPullback_properPushforward_comap C sX sY f hbase r hf k W γ]
  have hfp := flatPullback_principalDivisorCycle C ((W.comap f).subschemeι ≫ sX)
    (W.subschemeι ≫ sY) (comapRestrict W f) hbq r hqr hDim gg hgg
  have hdeg : (flatPullback C ((W.comap f).subschemeι ≫ sX) (W.subschemeι ≫ sY)
      (comapRestrict W f) hbq r hqr k γ).1 =
      (flatPullback C ((W.comap f).subschemeι ≫ sX) (W.subschemeι ≫ sY)
        (comapRestrict W f) hbq r hqr (k + 1 - 1)
        (principalDivisorCycle C (W.subschemeι ≫ sY) hDim gg)).1 := by
    refine Function.locallyFinsuppWithin.ext fun z ↦ ?_
    rw [flatPullback_apply, flatPullback_apply, show k + 1 - 1 + (r : ℤ) = k + r by ring]
    rfl
  show principalDivisorPushforward C sX (W.comap f) hW'int g' w =
    AlgebraicCycle.map (W.comap f).subschemeι
      (relativeDimension C.dimensionFunction ((W.comap f).subschemeι ≫ sX))
      (relativeDimension C.dimensionFunction sX)
      (flatPullback C ((W.comap f).subschemeι ≫ sX) (W.subschemeι ≫ sY)
        (comapRestrict W f) hbq r hqr k γ).1 w
  rw [hdeg, hfp, principalDivisorPushforward, hg']
  rfl

include hbase hb in
/-- **The divisor differential commutes with pulling back along an affine-space bundle.** For an
affine-space bundle `f : X ⟶ Y` of rank `r` and a locally finite family `a` of degree-one Milnor
K-classes at the points of `Y` of relative dimension `k + 1`, `div_X (f^* a) = f^* (div_Y a)`,
where `f^*` is `Stacks.Chow.bundleChainPullback` and `div` is the differential of Stacks 0GU3.

Coefficientwise both sides are locally finite sums over the points of relative dimension
`k + 1` of `Y`: on `X` only the generic points of the fibres contribute, and there the summands
agree by `Stacks.Chow.pointClosureOrd_milnorKTransport_of_isAffineSpaceBundle`. -/
theorem pointwiseDivisorDifferential_bundleChainPullback (k : ℤ) (a : PointwiseKOneGroup C sY k) :
    pointwiseDivisorDifferential C sX (k + r)
        (bundleChainPullback C sX sY f hbase hb (k + 1) (k + r + 1) (by ring) 1 a) =
      bundleChainPullback C sX sY f hbase hb k (k + r) rfl 0
        (pointwiseDivisorDifferential C sY k a) := by
  have := locallyOfFiniteType_of_isAffineSpaceBundle f r hb
  have := flat_of_isAffineSpaceBundle f r hb
  have hf := relativeDimension_of_isAffineSpaceBundle f r hb
  apply (pointwiseCycleEquiv C sX (k + r)).symm.injective
  have hRHS : pointwiseDivisorDifferential C sY k a =
      pointwiseCycleEquiv C sY k (pointwiseDivisorSum C sY k a) := rfl
  rw [hRHS, ← pointwiseCycleEquiv_flatPullback_of_isAffineSpaceBundle C sX sY f hbase hb hf,
    AddEquiv.symm_apply_apply, pointwiseCycleEquiv_symm_pointwiseDivisorDifferential]
  set b := bundleChainPullback C sX sY f hbase hb (k + 1) (k + r + 1) (by ring) 1 a with hbdef
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  show (pointwiseDivisorSum C sX (k + r) b).1 w =
    (flatPullback C sX sY f hbase r hf k (pointwiseDivisorSum C sY k a)).1 w
  rw [pointwiseDivisorSum_apply, flatPullback_apply, pointwiseDivisorSum_apply,
    finsum_mul]
  -- the generic points of the fibres over the points of relative dimension `k + 1`
  choose ξf hξf using exists_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb
  have hmem : ∀ y : pointsOfDimension C sY (k + 1), ξf y.1 ∈ pointsOfDimension C sX (k + r + 1) :=
    fun y ↦ by
      rw [mem_pointsOfDimension, (hξf y.1).2.1, (mem_pointsOfDimension C sY).mp y.2]
      ring
  have hdimf : ∀ y : Y, relativeDimension C.dimensionFunction sX (ξf y) =
      relativeDimension C.dimensionFunction sY (f.base (ξf y)) + r := fun y ↦ by
    rw [(hξf y).1]
    exact (hξf y).2.1
  set φ : pointsOfDimension C sY (k + 1) → pointsOfDimension C sX (k + r + 1) :=
    fun y ↦ ⟨ξf y.1, hmem y⟩ with hφ
  have hφinj : Function.Injective φ := fun y₁ y₂ h ↦ Subtype.ext <| by
    rw [← (hξf y₁.1).1, ← (hξf y₂.1).1]
    exact congrArg (fun ξ : pointsOfDimension C sX (k + r + 1) ↦ f.base ξ.1) h
  have hsupp : ∀ ξ, ξ ∉ Set.range φ → pointwiseDivisorTerm C sX (k + r) b ξ w = 0 := by
    intro ξ hξ
    by_contra hne
    have hbξ : b.1 ξ ≠ 0 := fun h0 ↦ hne (pointwiseDivisorTerm_apply_of_eq_zero C sX _ b h0 w)
    obtain ⟨hfξ, -⟩ := relativeDimension_eq_add_of_bundleChainPullback_ne_zero C sX sY f hbase hb
      (by ring) a hbξ
    refine hξ ⟨⟨f.base ξ.1, hfξ⟩, Subtype.ext ?_⟩
    refine eq_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb
      (hξf (f.base ξ.1)).1 (hdimf _) ?_
    rw [(mem_pointsOfDimension C sX).mp ξ.2, (mem_pointsOfDimension C sY).mp hfξ]
    ring
  rw [finsum_eq_finsum_of_injective φ hφinj _ hsupp]
  refine finsum_congr fun y ↦ ?_
  have hfy : f.base (φ y).1 ∈ pointsOfDimension C sY (k + 1) := by
    rw [show f.base (φ y).1 = y.1 from (hξf y.1).1]
    exact y.2
  rw [pointwiseDivisorTerm_apply_eq_pointClosureOrd, pointwiseDivisorTerm_apply_eq_pointClosureOrd,
    hbdef, bundleChainPullback_apply_of_mem C sX sY f hbase hb _ a (φ y) hfy,
    pointClosureOrd_milnorKTransport_of_isAffineSpaceBundle C sX sY f hbase hb hf
      (hdimf y.1) ((mem_pointsOfDimension C sY).mp hfy)]
  have key : ∀ y₁ y₂ : pointsOfDimension C sY (k + 1), y₁ = y₂ →
      pointClosureOrd C sY y₁.1 (a.1 y₁) (f.base w) =
        pointClosureOrd C sY y₂.1 (a.1 y₂) (f.base w) := by
    rintro _ _ rfl
    rfl
  exact congrArg (· * flatPullbackWeight C sX f (k + r) w)
    (key ⟨f.base (φ y).1, hfy⟩ y (Subtype.ext (hξf y.1).1))

end Bundle

end Stacks.Chow

end
