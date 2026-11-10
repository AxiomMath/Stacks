module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Normalized
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SectionDivisor
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegree
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.DegreeAtLeastGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicardSequence
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdd
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective

/-!
# Additivity of the fibre degree on the Picard functor of a curve

For a Picard class `x` on a curve `Z` over a field `K`, `Stacks.PicardCurve.classDegree` is its
degree, the degree homomorphism `AlgebraicGeometry.picardDegree` read through the identification
`Stacks.GluePicard.picardModelAddEquiv` of the two models of the Picard group; it is additive.

For a smooth projective geometrically irreducible curve `X` over `k` and a test scheme `T`, each
fibre `X_t` of `X_T ⟶ T` is a curve over `κ(t)`, and the fibre degree
`Stacks.PicardFunctor.fibreDegree` of a point of the Picard functor at `t` is the degree of the
pullback of a representing class to `X_t`. Translation by a section `g` of the Picard functor
over the base whose fibre degree is `e` gives an isomorphism `Pic^d_{X/k} ≅ Pic^{d+e}_{X/k}`.

## Main definitions

* `Stacks.PicardCurve.classDegree`: the degree of a Picard class of a curve over a field.
* `Stacks.PicardCurve.fibreClassDegree`: the degree of a Picard class of `X_T` on the fibre `X_t`.
* `Stacks.PicardFunctor.translateMorphism`: translation of `Pic_{X/k}` by a section over the base.
* `Stacks.PicardFunctor.picardDegreeComponentTranslateIso`: the translation isomorphism
  `Pic^d_{X/k} ≅ Pic^{d'}_{X/k}`.

## Main results

* `Stacks.PicardCurve.classDegree_add`, `Stacks.PicardCurve.classDegree_eq`.
* `Stacks.PicardCurve.isCurve_fibreAtProj`: the fibres of a base change of a curve are curves.
* `Stacks.PicardFunctor.fibreDegree_zero`, `Stacks.PicardFunctor.fibreDegree_neg`,
  `Stacks.PicardFunctor.fibreDegree_restrictBase_add`.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.FibreCohomology

universe u

namespace Stacks.PicardCurve

section Degree

variable (K : Type u) [Field K] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsProper g] [IsCurve K g]

/-- **The degree of a Picard class of a curve over a field**, as a homomorphism: the degree
homomorphism `AlgebraicGeometry.picardDegree` read through the identification of the two models
of the Picard group. -/
def classDegreeHom : Stacks.Picard.ofScheme Z →+ ℤ :=
  (picardDegree K g (IsCurve.topologicalKrullDim_eq_one (k := K) (f := g)).le).comp
    (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace).toAddMonoidHom

/-- **The degree of a Picard class of a curve over a field.** -/
def classDegree (x : Stacks.Picard.ofScheme Z) : ℤ := classDegreeHom K g x

/-- **The degree of Picard classes is additive** ([Stacks, Tag 0AYX] at rank one). -/
theorem classDegree_add (x y : Stacks.Picard.ofScheme Z) :
    classDegree K g (x + y) = classDegree K g x + classDegree K g y :=
  (classDegreeHom K g).map_add x y

/-- The trivial Picard class has degree zero. -/
theorem classDegree_zero : classDegree K g 0 = 0 :=
  (classDegreeHom K g).map_zero

/-- The degree of the inverse of a Picard class is the negative of its degree. -/
theorem classDegree_neg (x : Stacks.Picard.ofScheme Z) :
    classDegree K g (-x) = -classDegree K g x :=
  (classDegreeHom K g).map_neg x

/-- The degree of a Picard class is the degree of its chosen representative. -/
theorem classDegree_eq (x : Stacks.Picard.ofScheme Z) :
    classDegree K g x = @invertibleCurveDegree K _ Z g _
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := g)).le (rep x)
      (Stacks.TwoAffineCech.isInvertible_of_isInvertibleModule (rep x)) := by
  have h := Stacks.Picard.classOf_picardRepresentative Z.toRingedSpace x
  change picardDegree K g (IsCurve.topologicalKrullDim_eq_one (k := K) (f := g)).le
    (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace x) = _
  conv_lhs => rw [← h]
  rw [Stacks.GluePicard.picardModelAddEquiv_classOf]
  exact picardDegree_classOf K g _ (rep x) _

/-- **The Euler characteristic of a Picard class on a curve**: `χ(Z, L) = deg L + χ(Z, 𝒪_Z)`,
read on the chosen representative. -/
theorem euler_rep_eq (x : Stacks.Picard.ofScheme Z) :
    (Module.finrank K (cohomologyOverField K g (rep x) 0) : ℤ) -
        Module.finrank K (cohomologyOverField K g (rep x) 1) =
      classDegree K g x +
        ((Module.finrank K (cohomologyOverField K g (SheafOfModules.unit Z.ringCatSheaf) 0) : ℤ) -
          Module.finrank K (cohomologyOverField K g (SheafOfModules.unit Z.ringCatSheaf) 1)) := by
  have hdim := (IsCurve.topologicalKrullDim_eq_one (k := K) (f := g)).le
  have := Stacks.TwoAffineCech.isInvertible_of_isInvertibleModule (rep x)
  rw [classDegree_eq, invertibleCurveDegree_eq_sub_of_isZero K g hdim (rep x)
    (isZero_cohomologyOverField_of_two_le' K g hdim _)
    (isZero_cohomologyOverField_of_two_le' K g hdim _)]
  ring

/-- The representative of the trivial class has the Euler characteristic of `𝒪_Z`. -/
theorem euler_rep_zero :
    (Module.finrank K (cohomologyOverField K g (rep (0 : Stacks.Picard.ofScheme Z)) 0) : ℤ) -
        Module.finrank K (cohomologyOverField K g (rep (0 : Stacks.Picard.ofScheme Z)) 1) =
      (Module.finrank K (cohomologyOverField K g (SheafOfModules.unit Z.ringCatSheaf) 0) : ℤ) -
          Module.finrank K (cohomologyOverField K g (SheafOfModules.unit Z.ringCatSheaf) 1) := by
  rw [euler_rep_eq, classDegree_zero, zero_add]

/-- **The degree of a Picard class is the difference of the Euler characteristics** of its
representative and of the representative of the trivial class. -/
theorem classDegree_eq_euler_sub (x : Stacks.Picard.ofScheme Z) :
    classDegree K g x =
      ((Module.finrank K (cohomologyOverField K g (rep x) 0) : ℤ) -
          Module.finrank K (cohomologyOverField K g (rep x) 1)) -
        ((Module.finrank K (cohomologyOverField K g (rep (0 : Stacks.Picard.ofScheme Z)) 0) : ℤ) -
          Module.finrank K (cohomologyOverField K g (rep (0 : Stacks.Picard.ofScheme Z)) 1)) := by
  rw [euler_rep_eq, euler_rep_zero]
  ring

end Degree

section Fibre

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  {T XT : Scheme.{u}} (a : T ⟶ Spec (.of k)) (gT : XT ⟶ X) (fT : XT ⟶ T)
  (hT : IsPullback gT fT f a)
  [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]

omit [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] in
include hT in
/-- The fibres of a base change of the curve are proper over their residue fields. -/
theorem isProper_fibreAtProj (t : T) : IsProper (fibreAtProj fT t) :=
  let := residueAlgebra a t
  Stacks.AbelMap.isProper_of_isPullback (K := T.residueField t) f _ _
    (isPullback_fiber f a gT fT hT t)

include hT in
/-- **The fibres of a base change of the curve are curves over their residue fields.** -/
theorem isCurve_fibreAtProj (t : T) : IsCurve (T.residueField t) (fibreAtProj fT t) := by
  let := residueAlgebra a t
  have hZ := isPullback_fiber f a gT fT hT t
  exact @isCurve_of_topologicalKrullDim_eq_one (T.residueField t) _ _ (fibreAtProj fT t)
    (Stacks.AbelMap.isIntegral_of_isPullback (K := T.residueField t) f _ _ hZ)
    (isProper_fibreAtProj f a gT fT hT t)
    (Stacks.AbelMap.topologicalKrullDim_eq_one_of_isPullback (K := T.residueField t) f _ _ hZ)

/-- **The fibre degree of a Picard class** of `X_T` at `t ∈ T`: the degree on the curve `X_t`
over `κ(t)` of the pullback of the class. -/
def fibreClassDegree (x : Stacks.Picard.ofScheme XT) (t : T) : ℤ :=
  haveI := isProper_fibreAtProj f a gT fT hT t
  haveI := isCurve_fibreAtProj f a gT fT hT t
  classDegree (T.residueField t) (fibreAtProj fT t)
    (Stacks.Picard.schemePullbackClass (fibreAtMap fT t) x)

/-- The fibre degree of Picard classes is additive. -/
theorem fibreClassDegree_add (x y : Stacks.Picard.ofScheme XT) (t : T) :
    fibreClassDegree f a gT fT hT (x + y) t =
      fibreClassDegree f a gT fT hT x t + fibreClassDegree f a gT fT hT y t := by
  simp only [fibreClassDegree, Stacks.Picard.schemePullbackClass_add, classDegree_add]

/-- **The fibre degree of a Picard class is the difference of fibre Euler characteristics.** -/
theorem fibreClassDegree_eq (x : Stacks.Picard.ofScheme XT) (t : T) :
    fibreClassDegree f a gT fT hT x t =
      ((classFibreRank fT x t 0 : ℤ) - classFibreRank fT x t 1) -
        ((classFibreRank fT 0 t 0 : ℤ) - classFibreRank fT 0 t 1) := by
  have := isProper_fibreAtProj f a gT fT hT t
  have := isCurve_fibreAtProj f a gT fT hT t
  have h0 : Stacks.Picard.schemePullbackClass (fibreAtMap fT t)
      (0 : Stacks.Picard.ofScheme XT) = 0 :=
    map_zero (Stacks.Picard.schemePullbackClassHom (fibreAtMap fT t))
  rw [classFibreRank_eq_fibre, classFibreRank_eq_fibre, classFibreRank_eq_fibre,
    classFibreRank_eq_fibre, h0]
  exact classDegree_eq_euler_sub _ _ _

end Fibre

end Stacks.PicardCurve

namespace Stacks.PicardFunctor

open Stacks.PicardCurve

/-! ### The fibre degree of points of the Picard functor is additive -/

section Additive

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]

/-- **The fibre degree of the class of an invertible module** on `X_T` is the degree of its
pullback to the fibre curve `X_t`. -/
theorem fibreDegree_toPicardFunctorHom (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX hk f T) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreDegree B hX hk f σ hσ hOiso T (toPicardFunctorHom B hX hk f T x) t =
      fibreClassDegree (B.inclusion.map f) (B.inclusion.map T.hom) (pullback.fst _ _)
        (baseChangeProj B hX hk f T)
        (IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map T.hom)) x t := by
  rw [fibreClassDegree_eq, fibreDegree, fibreEuler, fibreEuler,
    ← map_zero (toPicardFunctorHom B hX hk f T), fibreRank_toPicardFunctorHom,
    fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom]

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
/-- The zero of the Picard functor has fibre degree zero. -/
theorem fibreDegree_zero (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreDegree B hX hk f σ hσ hOiso T 0 t = 0 :=
  sub_self _

/-- The fibre degree of the negative of a point is the negative of its fibre degree. -/
theorem fibreDegree_neg (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreDegree B hX hk f σ hσ hOiso T (-ξ) t = -fibreDegree B hX hk f σ hσ hOiso T ξ t := by
  have h := fibreDegree_add B hX hk f σ hσ hOiso T (-ξ) ξ t
  rw [neg_add_cancel, fibreDegree_zero] at h
  linarith

/-- **The fibre degree of a translate**: translating by a section `g` over the base whose
degree is `e` adds `e` to the fibre degree. -/
theorem fibreDegree_restrictBase_add (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (e : ℤ) (hg : ∀ t, fibreDegree B hX hk f σ hσ hOiso (baseObj B hk) g t = e)
    (T : BigFppfOver B (Spec (.of k)) hk) (ξ : (picardFunctor B hX hk f).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreDegree B hX hk f σ hσ hOiso T (restrictBase B hX hk f g T + ξ) t =
      e + fibreDegree B hX hk f σ hσ hOiso T ξ t := by
  rw [fibreDegree_add, restrictBase, fibreDegree_map, hg]

end Additive

/-! ### Translation by a section over the base -/

section Translation

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable]

omit [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
    [(picardFunctor B hX hk f).IsRepresentable] in
/-- Restriction of sections over the base to `T` is additive. -/
theorem restrictBase_add (g g' : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (T : BigFppfOver B (Spec (.of k)) hk) :
    restrictBase B hX hk f (g + g') T = restrictBase B hX hk f g T + restrictBase B hX hk f g' T :=
  picardFunctor_map_add B hX hk f _ g g'

omit [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
    [(picardFunctor B hX hk f).IsRepresentable] in
/-- The restriction of the zero section over the base is zero. -/
theorem restrictBase_zero (T : BigFppfOver B (Spec (.of k)) hk) :
    restrictBase B hX hk f 0 T = 0 :=
  picardFunctor_map_zero B hX hk f _

/-- **Translation of the Picard scheme by a section `g` over the base**: the morphism
`Pic_{X/k} ⟶ Pic_{X/k}` classifying `ξ ↦ g + ξ`. -/
def translateMorphism (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) :
    picardSchemeOver B hX hk f ⟶ picardSchemeOver B hX hk f :=
  (picardHomEquiv B hX hk f).symm
    (restrictBase B hX hk f g _ + universalPoint B hX hk f)

omit [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)] in
/-- A morphism followed by a translation classifies the translate of the point it classifies. -/
theorem picardHomEquiv_comp_translateMorphism
    (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) {T : BigFppfOver B (Spec (.of k)) hk}
    (φ : T ⟶ picardSchemeOver B hX hk f) :
    picardHomEquiv B hX hk f (φ ≫ translateMorphism B hX hk f g) =
      restrictBase B hX hk f g T + picardHomEquiv B hX hk f φ := by
  rw [(picardFunctor B hX hk f).representableBy.homEquiv_comp, translateMorphism,
    Equiv.apply_symm_apply, picardFunctor_map_add, map_restrictBase]
  congr 1
  rw [← (picardFunctor B hX hk f).representableBy.homEquiv_comp, Category.comp_id]

omit [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)] in
/-- Translation by the zero section is the identity. -/
theorem translateMorphism_zero : translateMorphism B hX hk f 0 = 𝟙 _ := by
  apply (picardHomEquiv B hX hk f).injective
  rw [← Category.id_comp (translateMorphism B hX hk f 0), picardHomEquiv_comp_translateMorphism,
    restrictBase_zero, zero_add]

omit [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)] in
/-- Translation by `g` followed by translation by `g'` is translation by `g + g'`. -/
theorem translateMorphism_comp (g g' : (picardFunctor B hX hk f).obj (op (baseObj B hk))) :
    translateMorphism B hX hk f g ≫ translateMorphism B hX hk f g' =
      translateMorphism B hX hk f (g + g') := by
  apply (picardHomEquiv B hX hk f).injective
  rw [picardHomEquiv_comp_translateMorphism,
    ← Category.id_comp (translateMorphism B hX hk f g), picardHomEquiv_comp_translateMorphism,
    ← Category.id_comp (translateMorphism B hX hk f (g + g')),
    picardHomEquiv_comp_translateMorphism, restrictBase_add]
  abel

/-- The inclusion of a degree component is a monomorphism. -/
instance mono_picardDegreeComponentι (d : ℤ) :
    Mono (picardSchemeDegreeComponentι B hX hk f σ hσ d) := by
  have : Mono (B.inclusion.map (picardSchemeDegreeComponentι B hX hk f σ hσ d).left) := by
    rw [inclusion_map_picardSchemeDegreeComponentι]
    exact (inferInstance : Mono (picardDegreeLocus B hX hk f σ hσ d).ι)
  have : Mono (picardSchemeDegreeComponentι B hX hk f σ hσ d).left :=
    B.inclusion.mono_of_mono_map this
  exact Over.mono_of_mono_left _

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- The point classified by the inclusion of `Pic^d_{X/k}` has degree `d` on every fibre. -/
theorem curveFibreDegree_picardDegreeComponentι (d : ℤ) (t) :
    curveFibreDegree B hX hk f σ hσ _
      (picardHomEquiv B hX hk f (picardSchemeDegreeComponentι B hX hk f σ hσ d)) t = d :=
  (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ
    (picardSchemeDegreeComponentι B hX hk f σ hσ d) d).1 ⟨𝟙 _, Category.id_comp _⟩ t

/-- If `g` has fibre degree `e` and `e + d = d'`, then translation by `g` restricted to
`Pic^d_{X/k}` factors through `Pic^{d'}_{X/k}`. -/
theorem exists_degreeTranslate (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) (e : ℤ)
    (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    ∃ ψ : picardSchemeDegreeComponent B hX hk f σ hσ d ⟶
        picardSchemeDegreeComponent B hX hk f σ hσ d',
      ψ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d' =
        picardSchemeDegreeComponentι B hX hk f σ hσ d ≫ translateMorphism B hX hk f g := by
  refine (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ _ d').2 fun t => ?_
  rw [picardHomEquiv_comp_translateMorphism, curveFibreDegree, fibreDegree_restrictBase_add _ _ _ _
    σ hσ _ g e hg, ← curveFibreDegree, curveFibreDegree_picardDegreeComponentι, h]

/-- **Translation `Pic^d_{X/k} ⟶ Pic^{d'}_{X/k}`** by a section `g` of degree `e = d' - d`
over the base. -/
def degreeTranslateHom (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) (e : ℤ)
    (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    picardSchemeDegreeComponent B hX hk f σ hσ d ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d' :=
  (exists_degreeTranslate B hX hk f σ hσ g e hg d d' h).choose

/-- The translation `Pic^d_{X/k} ⟶ Pic^{d'}_{X/k}` followed by the inclusion of `Pic^{d'}_{X/k}`
is the inclusion of `Pic^d_{X/k}` followed by translation of `Pic_{X/k}`. -/
@[reassoc]
theorem degreeTranslateHom_ι (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) (e : ℤ)
    (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    degreeTranslateHom B hX hk f σ hσ g e hg d d' h ≫
        picardSchemeDegreeComponentι B hX hk f σ hσ d' =
      picardSchemeDegreeComponentι B hX hk f σ hσ d ≫ translateMorphism B hX hk f g :=
  (exists_degreeTranslate B hX hk f σ hσ g e hg d d' h).choose_spec

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- If a section `g` over the base has fibre degree `e` everywhere, then `-g` has fibre degree
`-e` everywhere. -/
theorem curveFibreDegree_neg_of_eq (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (e : ℤ) (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (t) :
    curveFibreDegree B hX hk f σ hσ (baseObj B hk) (-g) t = -e := by
  rw [curveFibreDegree, fibreDegree_neg, ← curveFibreDegree, hg]

/-- **The translation isomorphism `Pic^d_{X/k} ≅ Pic^{d'}_{X/k}`** by a section `g` over the base
of degree `e = d' - d`, in the big fppf site over `k`; its inverse is translation by `-g`. -/
def picardDegreeComponentTranslateIso (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (e : ℤ) (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    picardSchemeDegreeComponent B hX hk f σ hσ d ≅
      picardSchemeDegreeComponent B hX hk f σ hσ d' where
  hom := degreeTranslateHom B hX hk f σ hσ g e hg d d' h
  inv := degreeTranslateHom B hX hk f σ hσ (-g) (-e)
    (curveFibreDegree_neg_of_eq B hX hk f σ hσ g e hg) d' d (by omega)
  hom_inv_id := by
    rw [← cancel_mono (picardSchemeDegreeComponentι B hX hk f σ hσ d), Category.assoc,
      degreeTranslateHom_ι, degreeTranslateHom_ι_assoc, translateMorphism_comp, add_neg_cancel,
      translateMorphism_zero, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (picardSchemeDegreeComponentι B hX hk f σ hσ d'), Category.assoc,
      degreeTranslateHom_ι, degreeTranslateHom_ι_assoc, translateMorphism_comp, neg_add_cancel,
      translateMorphism_zero, Category.comp_id, Category.id_comp]

/-- The translation isomorphism `Pic^d_{X/k} ≅ Pic^{d'}_{X/k}` followed by the inclusion of
`Pic^{d'}_{X/k}` is the inclusion of `Pic^d_{X/k}` followed by translation of `Pic_{X/k}`. -/
@[reassoc]
theorem degreeTranslateIso_hom_ι (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) (e : ℤ)
    (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    (picardDegreeComponentTranslateIso B hX hk f σ hσ g e hg d d' h).hom ≫
        picardSchemeDegreeComponentι B hX hk f σ hσ d' =
      picardSchemeDegreeComponentι B hX hk f σ hσ d ≫ translateMorphism B hX hk f g :=
  degreeTranslateHom_ι B hX hk f σ hσ g e hg d d' h

/-- **The translation isomorphism of schemes `Pic^d_{X/k} ≅ Pic^{d'}_{X/k}`** over `k`, the image
of `Stacks.PicardFunctor.picardDegreeComponentTranslateIso` in schemes. -/
def degreeTranslateSchemeIso (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) (e : ℤ)
    (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    (picardDegreeLocus B hX hk f σ hσ d : Scheme.{u}) ≅ picardDegreeLocus B hX hk f σ hσ d' :=
  B.inclusion.mapIso
    ((Over.forget _).mapIso (picardDegreeComponentTranslateIso B hX hk f σ hσ g e hg d d' h))

/-- The translation isomorphism of schemes commutes with the projections to `Spec k`. -/
@[reassoc]
theorem degreeTranslateSchemeIso_hom_comp (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (e : ℤ) (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    (degreeTranslateSchemeIso B hX hk f σ hσ g e hg d d' h).hom ≫
        B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ d').hom =
      B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ d).hom :=
  (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map
      (Over.w (picardDegreeComponentTranslateIso B hX hk f σ hσ g e hg d d' h).hom))

/-- The translation isomorphism of schemes commutes with the inclusions into `Pic_{X/k}` and
the translation of `Pic_{X/k}`. -/
@[reassoc]
theorem degreeTranslateSchemeIso_hom_ι (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (e : ℤ) (hg : ∀ t, curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = e) (d d' : ℤ)
    (h : e + d = d') :
    (degreeTranslateSchemeIso B hX hk f σ hσ g e hg d d' h).hom ≫
        (picardDegreeLocus B hX hk f σ hσ d').ι =
      (picardDegreeLocus B hX hk f σ hσ d).ι ≫
        B.inclusion.map (translateMorphism B hX hk f g).left := by
  rw [← inclusion_map_picardSchemeDegreeComponentι, ← inclusion_map_picardSchemeDegreeComponentι]
  exact (B.inclusion.map_comp _ _).symm.trans ((congrArg (fun φ => B.inclusion.map φ.left)
    (degreeTranslateIso_hom_ι B hX hk f σ hσ g e hg d d' h)).trans (B.inclusion.map_comp _ _))

end Translation

end Stacks.PicardFunctor
