module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.OverScheme
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.CurveCover
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardBasePoints
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PointedCurveStructureSheaf
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# The degree components of the Picard scheme of a curve

Let `X` be a proper scheme of dimension at most one over a field `k` with a rational point `σ`,
and assume the hypothesis of [Stacks, Tag 0B9N] (`𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every test scheme),
which [Stacks, Tag 0B9U] supplies for a smooth projective curve. Every point `ξ` of the Picard
functor `Pic_{X/k}(T)` then lifts to an invertible module `L` on `X_T`, uniquely up to a twist
by an invertible module on `T` ([Stacks, Tag 0B9N]); since such a twist is trivial on every
fibre, the fibre cohomology dimensions `dim_{κ(t)} Hⁿ(X_t, L_t)` depend on `ξ` alone. This file
records them, and the fibre degree `deg(L_t) = χ(X_t, L_t) - χ(X_t, 𝒪_{X_t})`, which is locally
constant on `T` by the two-affine Čech engine
(`Stacks.TwoAffineCech.isLocallyConstant_fibreEuler_of_isPullback`).

When the Picard functor is representable, the fibre degree of the universal point is a locally
constant function on the Picard scheme, and its fibres are the degree components
`Pic^d_{X/k}`: open and closed subschemes, pairwise disjoint, covering, and representing the
points of degree `d` (the degree decomposition used in the proof of [Stacks, Tag 0BA0]).

## Main definitions

* `Stacks.PicardCurve.classFibreRank`: fibre cohomology dimensions of a Picard class.
* `Stacks.PicardFunctor.fibreRank`, `Stacks.PicardFunctor.fibreEuler`,
  `Stacks.PicardFunctor.fibreDegree`: the same for points of the Picard functor.
* `Stacks.PicardFunctor.degreeSubfunctor`: the degree-`d` subfunctor of the Picard functor.
* `Stacks.PicardFunctor.picardDegreeLocus`, `Stacks.PicardFunctor.picardSchemeDegreeComponent` and
  `Stacks.PicardFunctor.picardSchemeDegreeComponentι`: **`Pic^d_{X/k}`** as an open subscheme of the
  Picard scheme of a smooth projective curve, and as an object of the site with its inclusion.

## Main results

* `Stacks.PicardCurve.classFibreRank_add_schemePullbackClass`,
  `Stacks.PicardCurve.classFibreRank_schemePullbackClass`: fibre ranks ignore twists from the
  base and are compatible with base change.
* `Stacks.PicardFunctor.isLocallyConstant_fibreDegree`, `Stacks.PicardFunctor.fibreDegree_map`.
* `Stacks.PicardFunctor.isClopen_picardDegreeLocus`,
  `Stacks.PicardFunctor.disjoint_picardDegreeLocus`, `Stacks.PicardFunctor.iSup_picardDegreeLocus`,
  `Stacks.PicardFunctor.nonempty_isColimit_picardDegreeLocus`: the Picard scheme is the disjoint
  union of the open and closed subschemes `Pic^d_{X/k}`.
* `Stacks.PicardFunctor.exists_comp_picardSchemeDegreeComponentι_iff`: `Pic^d_{X/k}` represents the
  points of degree `d`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9U](https://stacks.math.columbia.edu/tag/0B9U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.FibreCohomology

universe u

namespace Stacks.PicardCurve

variable {Y Y' T : Scheme.{u}}

/-- The chosen invertible module representing a Picard class of a scheme. -/
abbrev rep (x : Stacks.Picard.ofScheme Y) : Y.Modules :=
  (Stacks.Picard.picardRepresentative Y.toRingedSpace x).obj

/-- The representative of a Picard class is an invertible module. -/
instance (x : Stacks.Picard.ofScheme Y) : Stacks.Ample.IsInvertibleModule Y (rep x) :=
  (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property

/-- The representative of a Picard class is quasi-coherent. -/
instance (x : Stacks.Picard.ofScheme Y) : (rep x).IsQuasicoherent :=
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- The representative of the class of an invertible module is isomorphic to it. -/
theorem nonempty_rep_picardClass_iso (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L) :
    Nonempty (rep (Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL) ≅ L) :=
  (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
    (Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace _)

/-- The representative of a pulled-back class is isomorphic to the pullback of the
representative. -/
theorem nonempty_rep_schemePullbackClass_iso (g : Y' ⟶ Y) (x : Stacks.Picard.ofScheme Y) :
    Nonempty (rep (Stacks.Picard.schemePullbackClass g x) ≅
      (Scheme.Modules.pullback g).obj (rep x)) := by
  obtain ⟨e⟩ := nonempty_rep_picardClass_iso (Y := Y')
    ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj (rep x))
    (Stacks.RingedSpace.modulePullback_isInvertible_of g.toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property)
  exact ⟨e ≪≫ ((Stacks.ProjectiveBundleQuotients.pullbackIso g).app (rep x)).symm⟩

end Stacks.PicardCurve

namespace Stacks.PicardCurve

variable {Y Y' T : Scheme.{u}}

/-- Isomorphic modules have fibre cohomology of the same dimension. -/
theorem finrank_fibreCohomology_congr (fT : Y ⟶ T) {L L' : Y.Modules} (e : L ≅ L') (t : T)
    (n : ℕ) :
    Module.finrank (T.residueField t) (fibreCohomology fT L t n) =
      Module.finrank (T.residueField t) (fibreCohomology fT L' t n) :=
  LinearEquiv.finrank_eq (cohomologyOverFieldMapIso (T.residueField t) (fibreAtProj fT t)
    ((Scheme.Modules.pullback (fibreAtMap fT t)).mapIso e) n).toLinearEquiv

/-- **The fibre rank of a Picard class**: `dim_{κ(t)} Hⁿ(Y_t, L_t)` for any invertible module `L`
in the class `x`, computed on the chosen representative. -/
def classFibreRank (fT : Y ⟶ T) (x : Stacks.Picard.ofScheme Y) (t : T) (n : ℕ) : ℕ :=
  Module.finrank (T.residueField t) (fibreCohomology fT (rep x) t n)

/-- The fibre rank of the class of an invertible module is the fibre rank of the module. -/
theorem classFibreRank_picardClass (fT : Y ⟶ T) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L) (t : T) (n : ℕ) :
    classFibreRank fT (Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL) t n =
      Module.finrank (T.residueField t) (fibreCohomology fT L t n) :=
  finrank_fibreCohomology_congr fT (nonempty_rep_picardClass_iso L hL).some t n

/-- The fibre rank of a class is read on the pullback of the class to the fibre. -/
theorem classFibreRank_eq_fibre (fT : Y ⟶ T) (x : Stacks.Picard.ofScheme Y) (t : T) (n : ℕ) :
    classFibreRank fT x t n =
      Module.finrank (T.residueField t) (cohomologyOverField (T.residueField t)
        (fibreAtProj fT t) (rep (Stacks.Picard.schemePullbackClass (fibreAtMap fT t) x)) n) :=
  LinearEquiv.finrank_eq (cohomologyOverFieldMapIso (T.residueField t) (fibreAtProj fT t)
    (nonempty_rep_schemePullbackClass_iso (fibreAtMap fT t) x).some.symm n).toLinearEquiv

/-- **Fibre ranks are insensitive to twisting by a class from the base**: on each fibre the
pullback of an invertible module on `T` is trivial, `Pic` of a field vanishing. -/
theorem classFibreRank_add_schemePullbackClass (fT : Y ⟶ T) (x : Stacks.Picard.ofScheme Y)
    (y : Stacks.Picard.ofScheme T) (t : T) (n : ℕ) :
    classFibreRank fT (x + Stacks.Picard.schemePullbackClass fT y) t n =
      classFibreRank fT x t n := by
  rw [classFibreRank_eq_fibre, classFibreRank_eq_fibre, Stacks.Picard.schemePullbackClass_add,
    Stacks.Picard.schemePullbackClass_comp, pullback.condition,
    ← Stacks.Picard.schemePullbackClass_comp]
  have : Subsingleton (Stacks.Picard.ofScheme (Spec (T.residueField t))) :=
    AlgebraicGeometry.subsingleton_picardGroup_spec_field (T.residueField t)
  rw [Subsingleton.elim (Stacks.Picard.schemePullbackClass (T.fromSpecResidueField t) y) 0]
  have h0 : Stacks.Picard.schemePullbackClass (pullback.snd fT (T.fromSpecResidueField t))
      (0 : Stacks.Picard.ofScheme (Spec (T.residueField t))) = 0 :=
    map_zero (Stacks.Picard.schemePullbackClassHom (pullback.snd fT (T.fromSpecResidueField t)))
  rw [h0, add_zero]

/-- **Fibre ranks are compatible with base change.** -/
theorem classFibreRank_schemePullbackClass (fT : Y ⟶ T) [IsProper fT] {S : Scheme.{u}}
    (q : Y' ⟶ Y) (f' : Y' ⟶ S) (h : S ⟶ T) (hq : IsPullback q f' fT h)
    (x : Stacks.Picard.ofScheme Y) (s : S) (n : ℕ) :
    classFibreRank f' (Stacks.Picard.schemePullbackClass q x) s n = classFibreRank fT x (h s) n :=
  finrank_fibreCohomology_eq_of_isPullback fT (rep x) q f' h hq _
    (nonempty_rep_schemePullbackClass_iso q x).some s n

end Stacks.PicardCurve

namespace Stacks.PicardFunctor

open Stacks.PicardCurve

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS) (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)
  (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)

/-- If `X ⟶ S` is proper, then so is its base change `X_T ⟶ T` to every test scheme `T`. -/
instance [IsProper (B.inclusion.map f)] (T : BigFppfOver B S hS) :
    IsProper (baseChangeProj B hX hS f T) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›

/-- The base change square of a morphism of test schemes is cartesian. -/
theorem isPullback_baseChangeMap {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    IsPullback (baseChangeMap B hX hS f g) (baseChangeProj B hX hS f T)
      (baseChangeProj B hX hS f U) (B.inclusion.map g.left) := by
  have hU := IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map U.hom)
  have hT := IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map T.hom)
  have hg : B.inclusion.map g.left ≫ B.inclusion.map U.hom = B.inclusion.map T.hom := by
    rw [← Functor.map_comp, Over.w g]
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := B.inclusion.map U.hom) ?_ ?_ hU
  · have hfst : baseChangeMap B hX hS f g ≫ pullback.fst _ _ = pullback.fst (B.inclusion.map f)
        (B.inclusion.map T.hom) := by
      simp only [baseChangeMap, pullback.lift_fst, Category.comp_id]
    rw [hfst, hg]; exact hT
  · simp only [baseChangeMap, baseChangeProj, pullback.lift_snd]

include σ hσ hOiso in
/-- Two classes with the same image in the Picard functor differ by a class from the base. -/
theorem exists_eq_add_of_toPicardFunctorHom_eq (T : BigFppfOver B S hS)
    {x x' : picardAt B hX hS f T}
    (h : toPicardFunctorHom B hX hS f T x = toPicardFunctorHom B hX hS f T x') :
    ∃ y, x' = x + Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T) y := by
  have hz : toPicardFunctorHom B hX hS f T (x' - x) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom
    B hX hS f σ hσ hOiso T (x' - x)).1 hz
  exact ⟨y, by rw [hy, add_sub_cancel]⟩

/-- **The fibre rank of a point of the Picard functor**: `dim_{κ(t)} Hⁿ(X_t, L_t)` for any
invertible module `L` on `X_T` whose class is the given point; see
`Stacks.PicardFunctor.fibreRank_toPicardFunctorHom`. -/
def fibreRank (T : BigFppfOver B S hS) (ξ : (picardFunctor B hX hS f).obj (Opposite.op T))
    (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℕ) : ℕ :=
  classFibreRank (baseChangeProj B hX hS f T)
    (Function.surjInv (surjective_toPicardFunctorHom B hX hS f σ hσ hOiso T) ξ) t n

/-- The fibre rank of the class of an invertible module is its fibre cohomology dimension. -/
theorem fibreRank_toPicardFunctorHom (T : BigFppfOver B S hS) (x : picardAt B hX hS f T)
    (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℕ) :
    fibreRank B hX hS f σ hσ hOiso T (toPicardFunctorHom B hX hS f T x) t n =
      classFibreRank (baseChangeProj B hX hS f T) x t n := by
  obtain ⟨y, hy⟩ := exists_eq_add_of_toPicardFunctorHom_eq B hX hS f σ hσ hOiso T
    (Function.surjInv_eq (surjective_toPicardFunctorHom B hX hS f σ hσ hOiso T)
      (toPicardFunctorHom B hX hS f T x)).symm
  rw [fibreRank, hy, classFibreRank_add_schemePullbackClass]

/-- The canonical map to the Picard functor is natural in the test scheme. -/
theorem picardFunctor_map_toPicardFunctorHom {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (x : picardAt B hX hS f U) :
    (picardFunctor B hX hS f).map g.op (toPicardFunctorHom B hX hS f U x) =
      toPicardFunctorHom B hX hS f T (picardMap B hX hS f g x) :=
  (ConcreteCategory.congr_hom ((toPicardFunctor B hX hS f).naturality g.op) x).symm

/-- **Fibre ranks of points of the Picard functor are compatible with base change.** -/
theorem fibreRank_map [IsProper (B.inclusion.map f)] {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (ξ : (picardFunctor B hX hS f).obj (Opposite.op U))
    (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℕ) :
    fibreRank B hX hS f σ hσ hOiso T ((picardFunctor B hX hS f).map g.op ξ) t n =
      fibreRank B hX hS f σ hσ hOiso U ξ (B.inclusion.map g.left t) n := by
  obtain ⟨x, rfl⟩ := surjective_toPicardFunctorHom B hX hS f σ hσ hOiso U ξ
  rw [picardFunctor_map_toPicardFunctorHom, fibreRank_toPicardFunctorHom,
    fibreRank_toPicardFunctorHom]
  exact classFibreRank_schemePullbackClass _ _ _ _ (isPullback_baseChangeMap B hX hS f g) x t n

end Stacks.PicardFunctor

namespace Stacks.PicardFunctor

open Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
  [IsProper (B.inclusion.map f)]
  (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The fibre Euler characteristic** `χ(X_t, L_t) = h⁰ - h¹` of a point of the Picard functor
of a curve. -/
def fibreEuler (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (Opposite.op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : ℤ :=
  (fibreRank B hX hk f σ hσ hOiso T ξ t 0 : ℤ) - fibreRank B hX hk f σ hσ hOiso T ξ t 1

include hU hUaff in
/-- **The fibre Euler characteristic of a point of the Picard functor is locally constant.** -/
theorem isLocallyConstant_fibreEuler (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (Opposite.op T)) :
    IsLocallyConstant (fibreEuler B hX hk f σ hσ hOiso T ξ) := by
  obtain ⟨x, rfl⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ hOiso T ξ
  have h := Stacks.TwoAffineCech.isLocallyConstant_fibreEuler_of_isPullback
    (B.inclusion.map f) U hU hUaff (B.inclusion.map T.hom) _ _
    (IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map T.hom)) (rep x)
  have he : fibreEuler B hX hk f σ hσ hOiso T (toPicardFunctorHom B hX hk f T x) = fun t =>
      (Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
          (fibreCohomology (baseChangeProj B hX hk f T) (rep x) t 0) : ℤ) -
        Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
          (fibreCohomology (baseChangeProj B hX hk f T) (rep x) t 1) := by
    funext t
    rw [fibreEuler, fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom]
    rfl
  rw [he]
  exact h

omit [IsProper (B.inclusion.map f)] in
/-- The zero of the Picard functor is preserved by its restriction maps. -/
theorem picardFunctor_map_zero {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    (picardFunctor B hX hk f).map g.op 0 = 0 := by
  rw [← toPicardFunctor_app_zero B hX hk f T]
  show (picardFunctor B hX hk f).map g.op (toPicardFunctorHom B hX hk f T 0) = _
  rw [picardFunctor_map_toPicardFunctorHom]
  exact (congrArg (toPicardFunctorHom B hX hk f T') (map_zero (picardMapHom B hX hk f g))).trans
    (map_zero _)

/-- **The fibre degree** `deg(L_t) = χ(X_t, L_t) - χ(X_t, 𝒪)` of a point of the Picard functor
of a curve. -/
def fibreDegree (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (Opposite.op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : ℤ :=
  fibreEuler B hX hk f σ hσ hOiso T ξ t - fibreEuler B hX hk f σ hσ hOiso T 0 t

include hU hUaff in
/-- **The fibre degree of a point of the Picard functor is locally constant.** -/
theorem isLocallyConstant_fibreDegree (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (Opposite.op T)) :
    IsLocallyConstant (fibreDegree B hX hk f σ hσ hOiso T ξ) :=
  (isLocallyConstant_fibreEuler B hX hk f σ hσ hOiso U hU hUaff T ξ).sub
    (isLocallyConstant_fibreEuler B hX hk f σ hσ hOiso U hU hUaff T 0)

/-- **The fibre degree is compatible with base change.** -/
theorem fibreDegree_map {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (ξ : (picardFunctor B hX hk f).obj (Opposite.op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T') :
    fibreDegree B hX hk f σ hσ hOiso T' ((picardFunctor B hX hk f).map g.op ξ) t =
      fibreDegree B hX hk f σ hσ hOiso T ξ (B.inclusion.map g.left t) := by
  have h0 := picardFunctor_map_zero B hX hk f g
  simp only [fibreDegree, fibreEuler]
  conv_lhs => rw [← h0]
  simp only [fibreRank_map]

/-- **The degree-`d` subfunctor of the Picard functor of a curve**: the points all of whose fibres
have degree `d`. -/
def degreeSubfunctor (d : ℤ) : Subfunctor (picardFunctor B hX hk f) where
  obj T := {ξ | ∀ t, fibreDegree B hX hk f σ hσ hOiso T.unop ξ t = d}
  map {T T'} g ξ hξ t := by
    change fibreDegree B hX hk f σ hσ hOiso T'.unop
      ((picardFunctor B hX hk f).map g.unop.op ξ) t = d
    rw [fibreDegree_map]
    exact hξ _

end Stacks.PicardFunctor

namespace Stacks.PicardFunctor

open Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
  [IsProper (B.inclusion.map f)] [X.IsSeparated] [IsNoetherian X]
  (hdim : topologicalKrullDim X ≤ 1)

section Representable

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- The universal point of the Picard functor over the Picard scheme. -/
abbrev universalPoint :
    (picardFunctor B hX hk f).obj (Opposite.op (picardSchemeOver B hX hk f)) :=
  picardHomEquiv B hX hk f (𝟙 _)

omit [IsProper (B.inclusion.map f)] [X.IsSeparated] [AlgebraicGeometry.IsNoetherian X] in
/-- A morphism to the Picard scheme classifies the pullback of the universal point. -/
theorem picardHomEquiv_eq_map {T : BigFppfOver B (Spec (.of k)) hk}
    (φ : T ⟶ picardSchemeOver B hX hk f) :
    picardHomEquiv B hX hk f φ =
      (picardFunctor B hX hk f).map φ.op (universalPoint B hX hk f) := by
  rw [← (picardFunctor B hX hk f).representableBy.homEquiv_comp φ (𝟙 _), Category.comp_id]

omit [X.IsSeparated] [AlgebraicGeometry.IsNoetherian X] in
/-- The fibre degree of the point classified by a morphism to the Picard scheme is the fibre
degree of the universal point at the image. -/
theorem fibreDegree_picardHomEquiv {T : BigFppfOver B (Spec (.of k)) hk}
    (φ : T ⟶ picardSchemeOver B hX hk f) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreDegree B hX hk f σ hσ hOiso T (picardHomEquiv B hX hk f φ) t =
      fibreDegree B hX hk f σ hσ hOiso _ (universalPoint B hX hk f)
        (B.inclusion.map φ.left t) := by
  rw [picardHomEquiv_eq_map, fibreDegree_map]

include hdim in
/-- The fibre degree of the universal point is locally constant on the Picard scheme. -/
theorem isLocallyConstant_fibreDegree_universalPoint :
    IsLocallyConstant (fibreDegree B hX hk f σ hσ hOiso _ (universalPoint B hX hk f)) := by
  obtain ⟨U, hU, hUaff⟩ := Stacks.TwoAffineCech.exists_cover_isAffineOpen X hdim
  exact isLocallyConstant_fibreDegree B hX hk f σ hσ hOiso U hU hUaff _ _

include hdim in
/-- The locus of the Picard scheme where the universal point has fibre degree `d` is open. -/
theorem isOpen_degreeLocus (d : ℤ) :
    IsOpen {p : picardScheme B hX hk f |
      fibreDegree B hX hk f σ hσ hOiso _ (universalPoint B hX hk f) p = d} :=
  (isLocallyConstant_fibreDegree_universalPoint B hX hk f σ hσ hOiso hdim).isOpen_fiber d

/-- **`Pic^d_{X/k}`, the degree-`d` component of the Picard scheme of a curve**, as an open
subscheme: the points at which the universal invertible module has degree `d`. -/
def degreeLocus (d : ℤ) : (picardScheme B hX hk f).Opens :=
  ⟨_, isOpen_degreeLocus B hX hk f σ hσ hOiso hdim d⟩

/-- A point lies in `Pic^d_{X/k}` exactly when the universal point has fibre degree `d` there. -/
theorem mem_degreeLocus {d : ℤ} (p : picardScheme B hX hk f) :
    p ∈ degreeLocus B hX hk f σ hσ hOiso hdim d ↔
      fibreDegree B hX hk f σ hσ hOiso _ (universalPoint B hX hk f) p = d :=
  Iff.rfl

/-- **`Pic^d_{X/k}` is closed as well as open.** -/
theorem isClopen_degreeLocus (d : ℤ) :
    IsClopen (degreeLocus B hX hk f σ hσ hOiso hdim d : Set (picardScheme B hX hk f)) :=
  (isLocallyConstant_fibreDegree_universalPoint B hX hk f σ hσ hOiso hdim).isClopen_fiber d

/-- The degree components are pairwise disjoint. -/
theorem disjoint_degreeLocus {d e : ℤ} (hde : d ≠ e) :
    Disjoint (degreeLocus B hX hk f σ hσ hOiso hdim d)
      (degreeLocus B hX hk f σ hσ hOiso hdim e) := by
  rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
  exact fun p hp hp' => hde (hp.symm.trans hp')

/-- The degree components cover the Picard scheme. -/
theorem iSup_degreeLocus : ⨆ d, degreeLocus B hX hk f σ hσ hOiso hdim d = ⊤ := by
  refine eq_top_iff.2 fun p _ => ?_
  rw [TopologicalSpace.Opens.mem_iSup]
  exact ⟨_, rfl⟩

/-- **A morphism to the Picard scheme lands in `Pic^d_{X/k}` exactly when the point it
classifies has degree `d` on every fibre.** -/
theorem range_subset_degreeLocus_iff {T : BigFppfOver B (Spec (.of k)) hk}
    (φ : T ⟶ picardSchemeOver B hX hk f) (d : ℤ) :
    Set.range (B.inclusion.map φ.left) ⊆ degreeLocus B hX hk f σ hσ hOiso hdim d ↔
      picardHomEquiv B hX hk f φ ∈
        (degreeSubfunctor B hX hk f σ hσ hOiso d).obj (Opposite.op T) := by
  constructor
  · intro h t
    rw [fibreDegree_picardHomEquiv]
    exact h ⟨t, rfl⟩
  · rintro h _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, mem_degreeLocus, ← fibreDegree_picardHomEquiv]
    exact h t

end Representable

end Stacks.PicardFunctor

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

section Curve

variable [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)]

include σ hσ in
/-- **Tag 0B9U, read on the site**: for a smooth projective curve with a rational point the
hypothesis of Tag 0B9N holds at every test scheme. -/
theorem isIso_baseChangeProj_c_of_isCurve (T : BigFppfOver B (Spec (.of k)) hk) :
    IsIso (baseChangeProj B hX hk f T).toLRSHom.toHom.c :=
  isIso_c_baseChange_of_isCurve_of_section (B.inclusion.map f) σ hσ (B.inclusion.map T.hom)

omit [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)] in
include f in
/-- A projective variety over `k` is a separated scheme. -/
theorem isSeparated_of_isCurve : X.IsSeparated :=
  ⟨by
    have h : B.inclusion.map f ≫ terminal.from (Spec (.of k)) = terminal.from X :=
      terminal.comp_from _
    have h1 : IsSeparated (B.inclusion.map f) := IsVariety.toIsSeparated (k := k)
    have h2 : IsSeparated (terminal.from (Spec (.of k))) :=
      Scheme.IsSeparated.isSeparated_terminal_from
    have : IsSeparated (B.inclusion.map f ≫ terminal.from (Spec (.of k))) := inferInstance
    exact h ▸ this⟩

omit [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)] in
include f in
/-- A projective variety over `k` is a Noetherian scheme. -/
theorem isNoetherian_of_isCurve : IsNoetherian X :=
  have : IsNoetherian (Spec (.of k)) := inferInstance
  isNoetherian_of_locallyOfFiniteType (Y := Spec (.of k)) (B.inclusion.map f)

omit [IsProjectiveVariety k (B.inclusion.map f)] [Smooth (B.inclusion.map f)] in
include f in
/-- A curve over `k` has topological Krull dimension at most one. -/
theorem topologicalKrullDim_le_one_of_isCurve : topologicalKrullDim X ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le

section Representable

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- **`Pic^d_{X/k}`, the degree-`d` component of the Picard scheme of a smooth projective curve**
with a rational point `σ`, as an open subscheme of the Picard scheme: the points at which the
universal invertible module has degree `d` on the fibre. -/
def picardDegreeLocus (d : ℤ) : (picardScheme B hX hk f).Opens :=
  haveI := isSeparated_of_isCurve B hX hk f
  haveI := isNoetherian_of_isCurve B hX hk f
  degreeLocus B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
    (topologicalKrullDim_le_one_of_isCurve B hX hk f) d

/-- The fibre degree of points of the Picard functor of a smooth projective curve. -/
abbrev curveFibreDegree (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (Opposite.op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : ℤ :=
  fibreDegree B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T ξ t

/-- A point lies in `Pic^d_{X/k}` exactly when the universal point has fibre degree `d` there. -/
theorem mem_picardDegreeLocus {d : ℤ} (p : picardScheme B hX hk f) :
    p ∈ picardDegreeLocus B hX hk f σ hσ d ↔
      curveFibreDegree B hX hk f σ hσ _ (universalPoint B hX hk f) p = d :=
  Iff.rfl

/-- **`Pic^d_{X/k}` is open and closed.** -/
theorem isClopen_picardDegreeLocus (d : ℤ) :
    IsClopen (picardDegreeLocus B hX hk f σ hσ d : Set (picardScheme B hX hk f)) :=
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  isClopen_degreeLocus B hX hk f σ hσ _ (topologicalKrullDim_le_one_of_isCurve B hX hk f) d

/-- The degree components are pairwise disjoint. -/
theorem disjoint_picardDegreeLocus {d e : ℤ} (hde : d ≠ e) :
    Disjoint (picardDegreeLocus B hX hk f σ hσ d) (picardDegreeLocus B hX hk f σ hσ e) :=
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  disjoint_degreeLocus B hX hk f σ hσ _ (topologicalKrullDim_le_one_of_isCurve B hX hk f) hde

/-- The degree components cover the Picard scheme. -/
theorem iSup_picardDegreeLocus : ⨆ d, picardDegreeLocus B hX hk f σ hσ d = ⊤ :=
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  iSup_degreeLocus B hX hk f σ hσ _ (topologicalKrullDim_le_one_of_isCurve B hX hk f)

/-- **A morphism to the Picard scheme lands in `Pic^d_{X/k}` exactly when the point it classifies
has degree `d` on every fibre.** -/
theorem range_subset_picardDegreeLocus_iff {T : BigFppfOver B (Spec (.of k)) hk}
    (φ : T ⟶ picardSchemeOver B hX hk f) (d : ℤ) :
    Set.range (B.inclusion.map φ.left) ⊆ picardDegreeLocus B hX hk f σ hσ d ↔
      ∀ t, curveFibreDegree B hX hk f σ hσ T (picardHomEquiv B hX hk f φ) t = d :=
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  range_subset_degreeLocus_iff B hX hk f σ hσ _ (topologicalKrullDim_le_one_of_isCurve B hX hk f)
    φ d

/-- **Tag 0BA0, clause (1), the disjoint-union half, unconditionally for the degree components**:
each inclusion `Pic^d_{X/k} ⟶ Pic_{X/k}` is a closed immersion. -/
theorem isClosedImmersion_picardDegreeLocus_ι (d : ℤ) :
    IsClosedImmersion (picardDegreeLocus B hX hk f σ hσ d).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact (isClopen_picardDegreeLocus B hX hk f σ hσ d).isClosed)

/-- **The Picard scheme is the disjoint union of its degree components.** -/
theorem nonempty_isColimit_picardDegreeLocus :
    Nonempty (IsColimit (Cofan.mk (picardScheme B hX hk f)
      fun d => (picardDegreeLocus B hX hk f σ hσ d).ι)) := by
  refine nonempty_isColimit_cofanMk_of _ ?_ fun a b hab => ?_
  · simpa only [Scheme.Opens.opensRange_ι] using iSup_picardDegreeLocus B hX hk f σ hσ
  · simpa only [Scheme.Opens.opensRange_ι] using disjoint_picardDegreeLocus B hX hk f σ hσ hab

/-- `Pic^d_{X/k}` is an object of the site. -/
theorem contains_picardDegreeLocus (d : ℤ) :
    B.Contains (picardDegreeLocus B hX hk f σ hσ d : Scheme.{u}) :=
  (Scheme.size_le_of_isOpenImmersion (picardDegreeLocus B hX hk f σ hσ d).ι).trans_lt
    (picardSchemeOver B hX hk f).left.2

/-- The scheme `Pic^d_{X/k}` as an object of the underlying category of the site. -/
abbrev degreeLocusObj (d : ℤ) : B.Schemes := B.obj (contains_picardDegreeLocus B hX hk f σ hσ d)

/-- The inclusion `Pic^d_{X/k} ⟶ Pic_{X/k}` in the underlying category of the site. -/
def degreeLocusHom (d : ℤ) :
    degreeLocusObj B hX hk f σ hσ d ⟶ (picardSchemeOver B hX hk f).left :=
  B.inclusion.preimage (X := degreeLocusObj B hX hk f σ hσ d)
    (Y := (picardSchemeOver B hX hk f).left) (picardDegreeLocus B hX hk f σ hσ d).ι

/-- The inclusion `degreeLocusHom` is the open immersion `Pic^d_{X/k} ⟶ Pic_{X/k}`. -/
theorem inclusion_map_degreeLocusHom (d : ℤ) :
    B.inclusion.map (degreeLocusHom B hX hk f σ hσ d) = (picardDegreeLocus B hX hk f σ hσ d).ι :=
  B.inclusion.map_preimage _

/-- **`Pic^d_{X/k}` as an object of the big fppf site over `k`.** -/
def picardSchemeDegreeComponent (d : ℤ) : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (degreeLocusHom B hX hk f σ hσ d ≫ (picardSchemeOver B hX hk f).hom)

/-- The inclusion `Pic^d_{X/k} ⟶ Pic_{X/k}` in the site. -/
def picardSchemeDegreeComponentι (d : ℤ) :
    picardSchemeDegreeComponent B hX hk f σ hσ d ⟶ picardSchemeOver B hX hk f :=
  Over.homMk (degreeLocusHom B hX hk f σ hσ d) rfl

/-- The underlying morphism of schemes of `picardSchemeDegreeComponentι` is the open immersion
`Pic^d_{X/k} ⟶ Pic_{X/k}`. -/
theorem inclusion_map_picardSchemeDegreeComponentι (d : ℤ) :
    B.inclusion.map (picardSchemeDegreeComponentι B hX hk f σ hσ d).left =
      (picardDegreeLocus B hX hk f σ hσ d).ι :=
  inclusion_map_degreeLocusHom B hX hk f σ hσ d

/-- **`Pic^d_{X/k}` represents the degree-`d` points of the Picard functor**: a morphism `T ⟶
Pic_{X/k}` factors through `Pic^d_{X/k}` exactly when the point of `Pic_{X/k}(T)` it classifies
has degree `d` on every fibre of `X_T ⟶ T`. -/
theorem exists_comp_picardSchemeDegreeComponentι_iff {T : BigFppfOver B (Spec (.of k)) hk}
    (φ : T ⟶ picardSchemeOver B hX hk f) (d : ℤ) :
    (∃ ψ : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d,
        ψ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d = φ) ↔
      ∀ t, curveFibreDegree B hX hk f σ hσ T (picardHomEquiv B hX hk f φ) t = d := by
  rw [← range_subset_picardDegreeLocus_iff]
  constructor
  · rintro ⟨ψ, rfl⟩ _ ⟨t, rfl⟩
    rw [Over.comp_left, Functor.map_comp, inclusion_map_picardSchemeDegreeComponentι,
      ← Scheme.Opens.range_ι]
    exact ⟨B.inclusion.map ψ.left t, rfl⟩
  · intro h
    let ℓ := IsOpenImmersion.lift (picardDegreeLocus B hX hk f σ hσ d).ι (B.inclusion.map φ.left)
      (by rwa [Scheme.Opens.range_ι])
    have hℓ : ℓ ≫ (picardDegreeLocus B hX hk f σ hσ d).ι = B.inclusion.map φ.left :=
      IsOpenImmersion.lift_fac _ _ _
    let ℓ' : T.left ⟶ degreeLocusObj B hX hk f σ hσ d :=
      B.inclusion.preimage (X := T.left) (Y := degreeLocusObj B hX hk f σ hσ d) ℓ
    have e1 : B.inclusion.map ℓ' = ℓ :=
      Functor.map_preimage (X := T.left) (Y := degreeLocusObj B hX hk f σ hσ d) B.inclusion ℓ
    have hleft : ℓ' ≫ degreeLocusHom B hX hk f σ hσ d = φ.left := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, e1, inclusion_map_degreeLocusHom, hℓ]
    refine ⟨Over.homMk ℓ' ?_, Over.OverMorphism.ext hleft⟩
    show ℓ' ≫ (degreeLocusHom B hX hk f σ hσ d ≫ (picardSchemeOver B hX hk f).hom) = T.hom
    rw [← Category.assoc, hleft]
    exact Over.w φ

end Representable

end Curve

end Stacks.PicardFunctor
