module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessChartPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessFieldFibreAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Condition (2) of Stacks 05WY

Work in Situation 05WX.  Condition (2) of Stacks 05WY asks: pick a morphism
`x : Spec(K) ⟶ X` representing the point, set `z = g ∘ x`, form the field fibres
`X_z = Spec(K) ×_{z, Z} X` and `Y_z = Spec(K) ×_{z, Z} Y` and let `F_z` be the pullback of `F`
to `X_z`; then `F_z` is flat at `x` over `Y_z`.

This file proves that condition equivalent to condition (1), and hence to condition (3).

## Main results

* `isFlatOverAtGeometricPoint_modulePullback_iff_isFibreFlatOverAtGeometricPoint`:
  **conditions (1) and (2) of Stacks 05WY**, over two composable cartesian squares whose
  lower-right intermediate space has a field étale local ring at the relevant point.  This is
  where the mathematics is; condition (2) is the case of the field fibre, where that space is
  `Spec(K)`.
* `isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`:
  **Stacks 05WY, conditions (1) and (2)**, with relative flatness at a point read at a geometric
  point as in Stacks 05VU.
* `AlgebraicGeometry.Space.isFlatOverAtPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`:
  the same with flatness at a point spelled by `AlgebraicGeometry.Space.IsFlatOverAtPoint`, the
  chartwise predicate of Definition 05VV that the source cites.
* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_exists_chartPoint`:
  **Stacks 05WY, conditions (2) and (3)**, composed through condition (1).
* `AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtGeometricPoint`: Definition 05VV at
  a point of `|X|` is condition (2) of Stacks 05VU at a geometric point above it.
* `AlgebraicGeometry.Space.flat_quotMaximalIdeal_etaleLocalRing_of_isPullback_of_isField` and
  `AlgebraicGeometry.Space.map_maximalIdeal_map_etaleLocalRingMap_eq_bot_of_point_eq`: the two
  facts the comparison needs about the right-hand column, in the spelling of the point of `Y`
  that condition (1) fixes.

## Implementation notes

The comparison itself is `Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessFieldFibreAlgebra.lean` composed with
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback_iff_flat_tensor` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChangeTensor.lean`: with `R`, `A` the étale
local rings of `Y` and `X`, `I = 𝔪_z̄ 𝒪_{Y, ȳ}`, and `R'`, `A'` those of `Y_z` and `X_z`, the
first says that `F_x̄/𝔪_z̄ F_x̄` is flat over `R/I` exactly when `A' ⊗_A F_x̄` is flat over `R'`,
and the second identifies the latter with condition (2) through the base-change formula of
Stacks 05VQ for the geometric stalk of a pullback.

The inputs the comparison needs about `R'` come from the lower square: `I` dies in `R'` because
the composite `𝒪_{Z, z̄} → 𝒪_{Y_z, ȳ_z}` factors through the field `𝒪_{Spec(K), k̄}`, and `R'` is
flat over the fibre `R/I` by `Module.Flat.quotMaximalIdeal_of_isPushout_of_isField`.  Both are
proved at the lower square's own spelling of the point of `Y` — `geometricPointMap (Y_z ⟶ Y) ȳ_z`
— and the predicate `AlgebraicGeometry.Space.IsFibreFlatOverAtGeometricPoint` of condition (1)
fixes it as `geometricPointMap f x̄` instead; the two agree by `congrArg` on the upper square's
`CategoryTheory.IsPullback.w`.  Since that is an equality of *geometric points* it moves the
index of `etaleLocalRing` and hence the types, so the transport is done by taking the point of
`Y` as a parameter carrying its defining equation and substituting, rather than by rewriting.
The homomorphism `R → R'` accordingly carries the `eqToHom` correction that
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback` and
`AlgebraicGeometry.Space.IsEtaleStalkTensorFlat` also carry.

The quotient algebra structures must be introduced with `let`, not `have`: the scalar towers
between them are proved from `IsScalarTower.of_algebraMap_eq` applied to
`Ideal.Quotient.lift_mk`, which needs the definition, and `have` discards it.

## References

* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05WX](https://stacks.math.columbia.edu/tag/05WX)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

open scoped TensorProduct

universe u

/-- An ideal that extends to `⊥` along a ring homomorphism is killed by it. -/
theorem Ideal.apply_eq_zero_of_map_eq_bot {R₀ S₀ : Type*} [CommRing R₀] [CommRing S₀]
    (ψ : R₀ →+* S₀) {I : Ideal R₀} (hI : I.map ψ = ⊥) {a : R₀} (ha : a ∈ I) : ψ a = 0 := by
  simpa [hI] using Ideal.mem_map_of_mem ψ ha

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism that factors through a space with field étale local ring kills the maximal
ideal of the target**, stated for a morphism presented together with a factorisation rather than
as a composite. -/
theorem map_maximalIdeal_etaleLocalRingMap_eq_bot_of_factors {W V Z : AlgebraicSpaces B S hS}
    (p : W ⟶ V) (q : V ⟶ Z) (m : W.1 ⟶ Z.1) (hm : m = p.hom ≫ q.hom)
    (w : GeometricPoint B S hS W.1)
    (hfield : IsField ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom w))) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1 (geometricPointMap m w)) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    (maximalIdeal ↥(etaleLocalRing B S hS Z.1 (geometricPointMap m w))).map
      (etaleLocalRingMap W.2 m w) = ⊥ := by
  subst hm
  exact map_maximalIdeal_etaleLocalRingMap_comp_eq_bot B S hS p q w hfield

/-- **The ideal `𝔪_z̄ 𝒪_{Y, ȳ}` dies in `𝒪_{Y', ȳ'}`**, for a square `q ≫ h = p ≫ ζ` whose
intermediate space `V` has field étale local ring at `v̄`, and for `ȳ` presented as any geometric
point of `Y` equal to the image of `ȳ'`. -/
theorem map_maximalIdeal_map_etaleLocalRingMap_eq_bot_of_point_eq
    {Y Y' V Z : AlgebraicSpaces B S hS} {q : Y' ⟶ Y} {p : Y' ⟶ V} {h : Y ⟶ Z} {ζ : V ⟶ Z}
    (hw : q.hom ≫ h.hom = p.hom ≫ ζ.hom) (y' : GeometricPoint B S hS Y'.1)
    (hfield : IsField ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom y')))
    (ybar : GeometricPoint B S hS Y.1) (hy : ybar = geometricPointMap q.hom y') :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom ybar)) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    ((maximalIdeal ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom ybar))).map
        (etaleLocalRingMap Y.2 h.hom ybar)).map
      ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) hy) ≫ CommRingCat.ofHom
        (etaleLocalRingMap Y'.2 q.hom y')).hom) = ⊥ := by
  subst hy
  rw [Ideal.map_map]
  simp only [eqToHom_refl, Category.id_comp, CommRingCat.hom_ofHom]
  rw [etaleLocalRingMap_comp Y'.2 Y.2 q.hom h.hom y']
  exact map_maximalIdeal_etaleLocalRingMap_eq_bot_of_factors B S hS p ζ (q.hom ≫ h.hom) hw y'
    hfield

/-- The transport of the maximal ideal of an étale local ring along an equality of geometric
points. -/
theorem map_maximalIdeal_eqToHom {Z : AlgebraicSpaces B S hS}
    {z₁ z₂ : GeometricPoint B S hS Z.1} (hz : z₁ = z₂) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1 z₁) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1 z₂) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    (maximalIdeal ↥(etaleLocalRing B S hS Z.1 z₁)).map
        (eqToHom (congrArg (etaleLocalRing B S hS Z.1) hz)).hom =
      maximalIdeal ↥(etaleLocalRing B S hS Z.1 z₂) := by
  subst hz
  simp

/-- A flat comparison `A ⊗_R R' → A'` restricting to the structure maps gives a pushout `T` of
`R → A` and `R → R'` which is a flat `A'`-algebra compatibly with the factors. -/
private theorem exists_flat_pushout_of_flat_tensor_hom.{a, b, c, d}
    {R : Type a} {A : Type b} {R' : Type c} {A' : Type d}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra A A'] [Algebra R' A']
    (φ : A ⊗[R] R' →+* A') (hl : φ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap A A')
    (hr : φ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap R' A')
    (hflat : φ.Flat) :
    ∃ (T : Type (max b c)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra A T)
      (_ : Algebra R' T) (_ : Algebra T A') (_ : IsScalarTower R A T) (_ : IsScalarTower R R' T)
      (_ : IsScalarTower A T A') (_ : IsScalarTower R' T A') (_ : Algebra.IsPushout R R' A T),
      Module.Flat T A' := by
  let : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  let : Algebra (A ⊗[R] R') A' := φ.toAlgebra
  have : IsScalarTower R R' (A ⊗[R] R') := Algebra.TensorProduct.right_isScalarTower
  have : IsScalarTower A (A ⊗[R] R') A' := IsScalarTower.of_algebraMap_eq' hl.symm
  have : IsScalarTower R' (A ⊗[R] R') A' := IsScalarTower.of_algebraMap_eq' hr.symm
  have : Algebra.IsPushout R R' A (A ⊗[R] R') := TensorProduct.isPushout.symm
  exact ⟨A ⊗[R] R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hflat⟩

/-- **Flatness of the upper-right corner of a cartesian square over the fibre of the base, for a
base change along a space with field étale local ring.**  Let

```
Y' --q--> Y
|p        |h
v         v
V --ζ---> Z
```

be a cartesian square of algebraic spaces, let `ȳ'` be a geometric point of `Y'` at which the
étale local ring of `V` is a field, and let `ȳ` be any geometric point of `Y` equal to the image
of `ȳ'`.  Then `𝒪_{Y', ȳ'}` is flat over the fibre `𝒪_{Y, ȳ}/𝔪_z̄ 𝒪_{Y, ȳ}`. -/
theorem flat_quotMaximalIdeal_etaleLocalRing_of_isPullback_of_isField
    {Y Y' V Z : AlgebraicSpaces B S hS} {q : Y' ⟶ Y} {p : Y' ⟶ V} {h : Y ⟶ Z} {ζ : V ⟶ Z}
    (hpb : IsPullback q p h ζ) (y' : GeometricPoint B S hS Y'.1)
    (hfield : IsField ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom y')))
    (ybar : GeometricPoint B S hS Y.1) (hy : ybar = geometricPointMap q.hom y') :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom ybar)) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    letI : Algebra ↥(etaleLocalRing B S hS Y.1 ybar) ↥(etaleLocalRing B S hS Y'.1 y') :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) hy) ≫ CommRingCat.ofHom
        (etaleLocalRingMap Y'.2 q.hom y')).hom).toAlgebra
    letI : Algebra (↥(etaleLocalRing B S hS Y.1 ybar) ⧸
        (maximalIdeal ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom ybar))).map
          (etaleLocalRingMap Y.2 h.hom ybar)) ↥(etaleLocalRing B S hS Y'.1 y') :=
      (Ideal.Quotient.lift _
        (algebraMap ↥(etaleLocalRing B S hS Y.1 ybar) ↥(etaleLocalRing B S hS Y'.1 y'))
        (fun _ ha => Ideal.apply_eq_zero_of_map_eq_bot _
          (map_maximalIdeal_map_etaleLocalRingMap_eq_bot_of_point_eq B S hS
            (congrArg (fun k : Y' ⟶ Z => k.hom) hpb.w) y' hfield ybar hy) ha)).toAlgebra
    Module.Flat (↥(etaleLocalRing B S hS Y.1 ybar) ⧸
        (maximalIdeal ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom ybar))).map
          (etaleLocalRingMap Y.2 h.hom ybar))
      ↥(etaleLocalRing B S hS Y'.1 y') := by
  subst hy
  let instZ : IsLocalRing
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom (geometricPointMap q.hom y'))) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
  have hw : q.hom ≫ h.hom = p.hom ≫ ζ.hom := congrArg (fun k : Y' ⟶ Z => k.hom) hpb.w
  have hzpt : geometricPointMap h.hom (geometricPointMap q.hom y') =
      geometricPointMap ζ.hom (geometricPointMap p.hom y') :=
    congrArg (fun k : Y' ⟶ Z => geometricPointMap k.hom y') hpb.w
  let instRA : Algebra
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom (geometricPointMap q.hom y')))
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y')) :=
    (etaleLocalRingMap Y.2 h.hom (geometricPointMap q.hom y')).toAlgebra
  let instRR' : Algebra
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom (geometricPointMap q.hom y')))
      ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom y')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Z.1) hzpt) ≫ CommRingCat.ofHom
      (etaleLocalRingMap V.2 ζ.hom (geometricPointMap p.hom y'))).hom).toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ := cartesian_etaleStalk_tensor_flat B S hS q p h ζ hpb y'
  let instAA' : Algebra ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y'))
      ↥(etaleLocalRing B S hS Y'.1 y') :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1)
      (rfl : geometricPointMap q.hom y' = geometricPointMap q.hom y')) ≫ CommRingCat.ofHom
        (etaleLocalRingMap Y'.2 q.hom y')).hom).toAlgebra
  have hB : (algebraMap ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y'))
      ↥(etaleLocalRing B S hS Y'.1 y')) = etaleLocalRingMap Y'.2 q.hom y' := by
    rw [RingHom.algebraMap_toAlgebra]
    simp
  let instQ : Algebra (↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y')) ⧸
      (maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap h.hom (geometricPointMap q.hom y')))).map
          (etaleLocalRingMap Y.2 h.hom (geometricPointMap q.hom y')))
      ↥(etaleLocalRing B S hS Y'.1 y') :=
    (Ideal.Quotient.lift _
      (algebraMap ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y'))
        ↥(etaleLocalRing B S hS Y'.1 y'))
      (fun _ ha => Ideal.apply_eq_zero_of_map_eq_bot _
        (map_maximalIdeal_map_etaleLocalRingMap_eq_bot_of_point_eq B S hS hw y' hfield _
          rfl) ha)).toAlgebra
  let instR'A' : Algebra ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom y'))
      ↥(etaleLocalRing B S hS Y'.1 y') := (etaleLocalRingMap Y'.2 p.hom y').toAlgebra
  obtain ⟨T, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    exists_flat_pushout_of_flat_tensor_hom φ (hleft.trans hB.symm) hright hflat
  let instRA' : Algebra
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom (geometricPointMap q.hom y')))
      ↥(etaleLocalRing B S hS Y'.1 y') :=
    (((algebraMap ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y'))
      ↥(etaleLocalRing B S hS Y'.1 y'))).comp
        (etaleLocalRingMap Y.2 h.hom (geometricPointMap q.hom y'))).toAlgebra
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom (geometricPointMap q.hom y')))
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y'))
      ↥(etaleLocalRing B S hS Y'.1 y') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom (geometricPointMap q.hom y')))
      ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom y'))
      ↥(etaleLocalRing B S hS Y'.1 y') := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => ?_)
    show (algebraMap ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y'))
        ↥(etaleLocalRing B S hS Y'.1 y'))
        ((etaleLocalRingMap Y.2 h.hom (geometricPointMap q.hom y')) a) = _
    rw [hB]
    refine (RingHom.congr_fun (etaleLocalRingMap_comp Y'.2 Y.2 q.hom h.hom y') a).trans ?_
    refine (RingHom.congr_fun (etaleLocalRingMap_eq_of_hom_eq B S hS Y'.2 hw y') a).trans ?_
    exact (RingHom.congr_fun (etaleLocalRingMap_comp Y'.2 V.2 p.hom ζ.hom y') _).symm
  let : IsScalarTower ↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y'))
      (↥(etaleLocalRing B S hS Y.1 (geometricPointMap q.hom y')) ⧸
        (maximalIdeal ↥(etaleLocalRing B S hS Z.1
          (geometricPointMap h.hom (geometricPointMap q.hom y')))).map
            (etaleLocalRingMap Y.2 h.hom (geometricPointMap q.hom y')))
      ↥(etaleLocalRing B S hS Y'.1 y') :=
    IsScalarTower.of_algebraMap_eq fun _ => (Ideal.Quotient.lift_mk _ _ _).symm
  have hdies : (maximalIdeal ↥(etaleLocalRing B S hS Z.1
      (geometricPointMap h.hom (geometricPointMap q.hom y')))).map
        (algebraMap ↥(etaleLocalRing B S hS Z.1
          (geometricPointMap h.hom (geometricPointMap q.hom y')))
          ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom y'))) = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra,
      show ((eqToHom (congrArg (etaleLocalRing B S hS Z.1) hzpt) ≫ CommRingCat.ofHom
          (etaleLocalRingMap V.2 ζ.hom (geometricPointMap p.hom y'))).hom) =
        (etaleLocalRingMap V.2 ζ.hom (geometricPointMap p.hom y')).comp
          (eqToHom (congrArg (etaleLocalRing B S hS Z.1) hzpt)).hom from rfl,
      ← Ideal.map_map, map_maximalIdeal_eqToHom B S hS hzpt]
    exact map_maximalIdeal_etaleLocalRingMap_eq_bot_of_isField B S hS ζ
      (geometricPointMap p.hom y') hfield
  exact Module.Flat.quotMaximalIdeal_of_isPushout_of_isField (T := T) hdies

/-- **Condition (1) of Stacks 05WY is the relative flatness of the base change along a morphism
with field étale local ring.**  Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
|p         |h
v          v
V --ζ----> Z
```

be two composable cartesian squares of algebraic spaces, let `F` be an `𝒪_X`-module and let `x̄'`
be a geometric point of `X'` at which the étale local ring of `V` is a field.  Then the pullback
of `F` to `X'` is flat over `Y'` at `x̄'` exactly when condition (1) of Stacks 05WY holds for
`X ⟶ Y ⟶ Z` at the image `x̄` of `x̄'`. -/
theorem isFlatOverAtGeometricPoint_modulePullback_iff_isFibreFlatOverAtGeometricPoint
    {X Y Z X' Y' V : AlgebraicSpaces B S hS}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {p : Y' ⟶ V} {h : Y ⟶ Z} {ζ : V ⟶ Z}
    (hU : IsPullback g' f' f g) (hL : IsPullback g p h ζ)
    (F : Modules.{u, u} B S hS X.1 X.2) (x' : GeometricPoint B S hS X'.1)
    (hfield : IsField ↥(etaleLocalRing B S hS V.1
      (geometricPointMap p.hom (geometricPointMap f'.hom x')))) :
    IsFlatOverAtGeometricPoint B S hS f' ((modulePullback B S hS g').obj F) x' ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F (geometricPointMap g'.hom x') := by
  have hwU : g'.hom ≫ f.hom = f'.hom ≫ g.hom := congrArg (fun k : X' ⟶ Y => k.hom) hU.w
  have hy : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hU.w
  let instZ : IsLocalRing ↥(etaleLocalRing B S hS Z.1
      (geometricPointMap h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x')))) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
  let instRA : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  let instRR' : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) hy) ≫ CommRingCat.ofHom
      (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ :=
    cartesian_etaleStalk_tensor_flat B S hS g' f' f g hU x'
  let instAA' : Algebra ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := (etaleLocalRingMap X'.2 g'.hom x').toAlgebra
  let instR'A' : Algebra ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := (etaleLocalRingMap X'.2 f'.hom x').toAlgebra
  obtain ⟨T, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    exists_flat_pushout_of_flat_tensor_hom φ hleft hright hflat
  let instRA' : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X'.1 x') :=
    ((etaleLocalRingMap X'.2 g'.hom x').comp
      (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x'))).toAlgebra
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => ?_)
    refine (RingHom.congr_fun (etaleLocalRingMap_comp X'.2 X.2 g'.hom f.hom x') a).trans ?_
    refine (RingHom.congr_fun (etaleLocalRingMap_eq_of_hom_eq B S hS X'.2 hwU x') a).trans ?_
    exact (RingHom.congr_fun (etaleLocalRingMap_comp X'.2 Y'.2 f'.hom g.hom x') _).symm
  let instQR' : Algebra (↥(etaleLocalRing B S hS Y.1
        (geometricPointMap f.hom (geometricPointMap g'.hom x'))) ⧸
      (maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))).map
          (etaleLocalRingMap Y.2 h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    (Ideal.Quotient.lift _
      (algebraMap ↥(etaleLocalRing B S hS Y.1
          (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')))
      (fun _ ha => Ideal.apply_eq_zero_of_map_eq_bot _
        (map_maximalIdeal_map_etaleLocalRingMap_eq_bot_of_point_eq B S hS
          (congrArg (fun k : Y' ⟶ Z => k.hom) hL.w) (geometricPointMap f'.hom x') hfield _
          hy) ha)).toAlgebra
  have : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      (↥(etaleLocalRing B S hS Y.1
          (geometricPointMap f.hom (geometricPointMap g'.hom x'))) ⧸
        (maximalIdeal ↥(etaleLocalRing B S hS Z.1
          (geometricPointMap h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))).map
            (etaleLocalRingMap Y.2 h.hom
              (geometricPointMap f.hom (geometricPointMap g'.hom x'))))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    IsScalarTower.of_algebraMap_eq fun _ => (Ideal.Quotient.lift_mk _ _ _).symm
  have : Module.Flat (↥(etaleLocalRing B S hS Y.1
        (geometricPointMap f.hom (geometricPointMap g'.hom x'))) ⧸
      (maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))).map
          (etaleLocalRingMap Y.2 h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    flat_quotMaximalIdeal_etaleLocalRing_of_isPullback_of_isField B S hS hL
      (geometricPointMap f'.hom x') hfield _ hy
  have : IsLocalRing ↥(etaleLocalRing B S hS X'.1 x') :=
    isLocalRing_etaleLocalRing B S hS X'.1 X'.2 x'
  have : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x')) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact isLocalHom_etaleLocalRingMap B S hS X'.2 X.2 g'.hom x'
  have : IsLocalRing (↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) ⧸
      ((maximalIdeal ↥(etaleLocalRing B S hS Z.1
          (geometricPointMap h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))).map
        (etaleLocalRingMap Y.2 h.hom
          (geometricPointMap f.hom (geometricPointMap g'.hom x')))).map
        (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x'))) := by
    rw [Ideal.map_map]
    let : Algebra ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
      ((etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).comp
        (etaleLocalRingMap Y.2 h.hom
          (geometricPointMap f.hom (geometricPointMap g'.hom x')))).toAlgebra
    have : IsLocalRing ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 _
    have : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap h.hom (geometricPointMap f.hom (geometricPointMap g'.hom x'))))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))) := by
      rw [RingHom.algebraMap_toAlgebra,
        etaleLocalRingMap_comp X.2 Y.2 f.hom h.hom (geometricPointMap g'.hom x')]
      exact isLocalHom_etaleLocalRingMap B S hS X.2 Z.2 (f.hom ≫ h.hom)
        (geometricPointMap g'.hom x')
    exact IsLocalRing.quotient_map_maximalIdeal
  refine (isFlatOverAtGeometricPoint_modulePullback_iff_flat_tensor B S hS hU F x').trans
    (Iff.trans (Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout (T := T)
      (M := ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F))
      ((maximalIdeal ↥(etaleLocalRing B S hS Z.1 (geometricPointMap h.hom
          (geometricPointMap f.hom (geometricPointMap g'.hom x'))))).map
        (etaleLocalRingMap Y.2 h.hom
          (geometricPointMap f.hom (geometricPointMap g'.hom x'))))).symm ?_)
  exact Module.flatQuotSMul_congr
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')) rfl (Ideal.map_map _ _) rfl
    (Ideal.map_map _ _).symm ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F)

/-- **Stacks 05VV at a point is Stacks 05VU condition (2) at a geometric point above it.**  For
a quasi-coherent `𝒪_X`-module `F` and a geometric point `x̄` of `X`, flatness of `F` over `Y` at
the image of `x̄` in `|X|`, in the chartwise sense of Definition 05VV, is flatness of the
geometric stalk `F_{x̄}` over `𝒪_{Y, ȳ}`. -/
theorem isFlatOverAtPoint_iff_isFlatOverAtGeometricPoint {Xs Ys : AlgebraicSpaces B S hS}
    (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS Xs.1) :
    IsFlatOverAtPoint B S hS Xs.2 f.hom F xbar.image ↔
      IsFlatOverAtGeometricPoint B S hS f F xbar := by
  rw [← isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint B S hS f F xbar]
  constructor
  · rintro ⟨d, u, hu, hflat⟩
    refine ⟨d, u, ?_, hflat⟩
    have hback : pointsToScheme B S hS d.U.obj.left
        ((pointsEquivScheme B S hS d.U.obj.left).symm u) = u :=
      (pointsEquivScheme B S hS d.U.obj.left).apply_symm_apply u
    exact hback ▸ hu ▸ chartPoint_pointsToScheme B S hS d.U.obj.left d.U.obj.hom
      ((pointsEquivScheme B S hS d.U.obj.left).symm u)
  · rintro ⟨d, u, ⟨p, hp, hx⟩, hflat⟩
    refine ⟨d, u, ?_, hflat⟩
    have hcls : (pointsEquivScheme B S hS d.U.obj.left).symm u =
        p.class B S hS (yoneda.obj d.U.obj.left) :=
      (pointsEquivScheme B S hS d.U.obj.left).symm_apply_eq.mpr
        (hp.symm.trans (pointsToScheme_class B S hS d.U.obj.left p))
    rwa [hcls]

/-! ### Stacks 05WY, condition (2) -/

/-- **Stacks 05WY: condition (2) if and only if condition (1).**  In Situation 05WX let `z` be a
field-valued point of `Z` with field of definition `K`, let `X_z = Spec(K) ×_{z, Z} X` and
`Y_z = Spec(K) ×_{z, Z} Y` be the field fibres and let `F_z` be the pullback of `F` to `X_z`.
Then for a geometric point `x̄_z` of `X_z`, the module `F_z` is flat over `Y_z` at `x̄_z` exactly
when condition (1) of Stacks 05WY holds at the image `x̄` of `x̄_z` in `X`.

This is condition (2) of the source.  Relative flatness at a point is read at a geometric point,
as condition (2) of Stacks 05VU
(`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`
identifies that with the chartwise condition of Definition 05VV which the source cites), and the
statement is at *every* geometric point of `X_z` rather than only at one above the `K`-rational
point `x` of `X_z` that the source's representative `x : Spec(K) ⟶ X` defines — which is the
source's condition (2) together with its independence of the choice of representative, since
condition (1) at the image of `x̄_z` depends only on that image
(`AlgebraicGeometry.Space.isFibreFlatOverAtGeometricPoint_congr_of_image_eq`). -/
@[stacks 05WY "(1) iff (2): flatness of the pullback of F to the field fibre X_z over Y_z at a \
geometric point of X_z, read at a geometric point as in Stacks 05VU, iff condition (1) at the \
image of that point in X"]
theorem isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (z : FieldValuedPoint B S hS Z.1)
    (xz : GeometricPoint B S hS (fieldFibreSpace (f ≫ h) z).1) :
    IsFlatOverAtGeometricPoint B S hS
        (ObjectProperty.homMk (fieldFibreSourceMap B S hS f.hom h.hom z) :
          fieldFibreSpace (f ≫ h) z ⟶ fieldFibreSpace h z)
        ((modulePullback B S hS (ObjectProperty.homMk
            (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
              fieldFibreSpace (f ≫ h) z ⟶ X)).obj F) xz ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F
        (geometricPointMap (ObjectProperty.homMk
          (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
            fieldFibreSpace (f ≫ h) z ⟶ X).hom xz) :=
  isFlatOverAtGeometricPoint_modulePullback_iff_isFibreFlatOverAtGeometricPoint B S hS
    (isPullback_fieldFibreSpace B S hS f h z) (isPullback_fieldFibreSpace_snd B S hS h z) F xz
    (isField_etaleLocalRing_yoneda (z.siteObject B S hS Z.1)
      (fun x => AlgebraicGeometry.isField_stalk_Spec_field z.carrier x) _)

/-- **Stacks 05WY, condition (2) against condition (1) at a chosen geometric point of `X`.**
Condition (2) at a geometric point `x̄_z` of the field fibre `X_z` holds exactly when
condition (1) holds at *any* geometric point `x̄` of `X` with the same image in `|X|` as the image
of `x̄_z`.

This is the form the source's condition (1) takes: "pick a geometric point `x̄` of `X` lying
over `x`". -/
@[stacks 05WY "(1) iff (2) with condition (1) at an arbitrary chosen geometric point of X above \
the point, as the source states condition (1)"]
theorem isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint_of_image_eq
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (z : FieldValuedPoint B S hS Z.1)
    (xz : GeometricPoint B S hS (fieldFibreSpace (f ≫ h) z).1)
    (xbar : GeometricPoint B S hS X.1)
    (himage : (geometricPointMap (ObjectProperty.homMk
        (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
          fieldFibreSpace (f ≫ h) z ⟶ X).hom xz).image = xbar.image) :
    IsFlatOverAtGeometricPoint B S hS
        (ObjectProperty.homMk (fieldFibreSourceMap B S hS f.hom h.hom z) :
          fieldFibreSpace (f ≫ h) z ⟶ fieldFibreSpace h z)
        ((modulePullback B S hS (ObjectProperty.homMk
            (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
              fieldFibreSpace (f ≫ h) z ⟶ X)).obj F) xz ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F xbar :=
  (isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint B S hS f h F z
    xz).trans (isFibreFlatOverAtGeometricPoint_congr_of_image_eq B S hS f h F _ xbar himage)

/-- **Stacks 05WY: condition (2) in the chartwise form of Definition 05VV, if and only if
condition (1).**  The pullback `F_z` of `F` to the field fibre `X_z` is flat at the image in
`|X_z|` of a geometric point `x̄_z`, over `Y_z`, in the sense of Definition 05VV, exactly when
condition (1) of Stacks 05WY holds at the image of `x̄_z` in `X`.

This is condition (2) with flatness at a point spelled by
`AlgebraicGeometry.Space.IsFlatOverAtPoint`, the predicate of Definition 05VV that the source
cites, rather than at a geometric point. -/
@[stacks 05WY "(1) iff (2) with condition (2) in the chartwise form of Definition 05VV, which \
is the predicate the source cites"]
theorem isFlatOverAtPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (z : FieldValuedPoint B S hS Z.1)
    (xz : GeometricPoint B S hS (fieldFibreSpace (f ≫ h) z).1) :
    IsFlatOverAtPoint B S hS (fieldFibreSpace (f ≫ h) z).2
        (ObjectProperty.homMk (fieldFibreSourceMap B S hS f.hom h.hom z) :
          fieldFibreSpace (f ≫ h) z ⟶ fieldFibreSpace h z).hom
        ((modulePullback B S hS (ObjectProperty.homMk
            (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
              fieldFibreSpace (f ≫ h) z ⟶ X)).obj F) xz.image ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F
        (geometricPointMap (ObjectProperty.homMk
          (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
            fieldFibreSpace (f ≫ h) z ⟶ X).hom xz) := by
  have : ((modulePullback B S hS (ObjectProperty.homMk
      (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
        fieldFibreSpace (f ≫ h) z ⟶ X)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F inferInstance
  exact (isFlatOverAtPoint_iff_isFlatOverAtGeometricPoint B S hS _ _ xz).trans
    (isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint B S hS f h F
      z xz)

/-- **Stacks 05WY: condition (2) if and only if condition (3).**  In Situation 05WX, flatness of
the pullback `F_z` over `Y_z` at a geometric point `x̄_z` of the field fibre `X_z` holds exactly
when there is a commuting diagram of schemes `U ⟶ V ⟶ W` étale over `f` and `h` and a point `u`
of `U` above the image of `x̄_z` in `|X|`, at which the fibre of `F|_U` over the fibre of `V` is
flat. -/
@[stacks 05WY "(2) iff (3), composed through condition (1); condition (3) carrying a point u of \
U above x as the source states it, read on the local rings of the charts"]
theorem isFlatOverAtGeometricPoint_fieldFibreSpace_iff_exists_chartPoint
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (z : FieldValuedPoint B S hS Z.1)
    (xz : GeometricPoint B S hS (fieldFibreSpace (f ≫ h) z).1) :
    IsFlatOverAtGeometricPoint B S hS
        (ObjectProperty.homMk (fieldFibreSourceMap B S hS f.hom h.hom z) :
          fieldFibreSpace (f ≫ h) z ⟶ fieldFibreSpace h z)
        ((modulePullback B S hS (ObjectProperty.homMk
            (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
              fieldFibreSpace (f ≫ h) z ⟶ X)).obj F) xz ↔
      ∃ (U : SmallEtale B S hS X.1) (Vc : SmallEtale B S hS Y.1) (Wc : SmallEtale B S hS Z.1)
          (g₁ : U.obj.left ⟶ Vc.obj.left)
          (_hcomm₁ : U.obj.hom ≫ f.hom = yoneda.map g₁ ≫ Vc.obj.hom)
          (g₂ : Vc.obj.left ⟶ Wc.obj.left)
          (_hcomm₂ : Vc.obj.hom ≫ h.hom = yoneda.map g₂ ≫ Wc.obj.hom)
          (u : chartScheme U),
        ChartPoint B S hS U.obj.left U.obj.hom u
            (geometricPointMap (ObjectProperty.homMk
              (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
                fieldFibreSpace (f ≫ h) z ⟶ X).hom xz).image ∧
          IsFibreFlatOnChartSquares B S hS X.1 X.2 F U Vc Wc g₁ g₂ u :=
  (isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint B S hS f h F z
    xz).trans
    (exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint B S hS f h F
      _).symm

end AlgebraicGeometry.Space

end
