module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of formally smooth, étale and unramified transformations

Fix a scheme in a big fppf site, three set-valued functors on its big fppf site, and two
natural transformations with common target. The fibre product of the two sources is again
such a functor, and the base change of the first transformation along the second is the
projection from the fibre product. That projection inherits formal smoothness, formal
étaleness and formal unramifiedness from the transformation it base changes.

## Main definitions

* `AlgebraicGeometry.Space.FppfFunctorPullbackSituation` bundles the site, the scheme, the
  functors and the two transformations.
* `AlgebraicGeometry.Space.FppfFunctorPullbackSituation.fibreProduct` and its projections
  `toH` and `toF` give the canonical base-change square.

## Main results

* `AlgebraicGeometry.Space.FppfFunctorPullbackSituation.isPullback` states the universal
  property of the square.
* `AlgebraicGeometry.Space.fibreProductLiftEquiv` is the bijection between lifts of a point
  of the fibre product over a prescribed point of `H` and compatible lifts of its `F`
  component, and `AlgebraicGeometry.Space.fibreProductLiftEquiv_apply` identifies its
  forward map with the second projection.
* `AlgebraicGeometry.Space.FormallySmooth.baseChange`,
  `AlgebraicGeometry.Space.formallyEtale_baseChange` and
  `AlgebraicGeometry.Space.formallyUnramified_baseChange` are the three base-change
  statements.

## Implementation notes

The diagram is the categorical pullback of `b` and `a` in the functor category, and the
first projection `toH` is the base change of `a` along `b`.

A point of the fibre product already contains the compatible pair of components, so the
bijection of lifts is characterized by the identity saying that its forward map is the
second projection; this makes the correspondence canonical. The underlying statement about
elements of a pullback of types holds for every morphism of test objects, not only for
affine square-zero closed immersions, and is proved here in that generality.

## References

* [Stacks Project, Tag 049U](https://stacks.math.columbia.edu/tag/049U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-- The data of a diagram of set-valued functors on the big fppf site of a scheme,
with two arrows to a common target. -/
public structure FppfFunctorPullbackSituation where
  /-- The chosen big fppf site. -/
  B : BigFppfSite.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The base scheme belongs to the chosen big fppf site. -/
  hS : B.Contains S
  /-- The functor to be base changed. -/
  F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v
  /-- The common target functor. -/
  G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v
  /-- The functor along which the base change is taken. -/
  H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v
  /-- The transformation to be base changed. -/
  a : F ⟶ G
  /-- The transformation along which the base change is taken. -/
  b : H ⟶ G

namespace FppfFunctorPullbackSituation

variable (D : FppfFunctorPullbackSituation.{u, v})

/-- The fibre product `H ×_G F` of the two functors. -/
public noncomputable def fibreProduct : (BigFppfOver D.B D.S D.hS)ᵒᵖ ⥤ Type v :=
  pullback D.b D.a

/-- The base-changed transformation from `H ×_G F` to `H`. -/
public noncomputable def toH : D.fibreProduct ⟶ D.H :=
  pullback.fst D.b D.a

/-- The projection from `H ×_G F` to `F`. -/
public noncomputable def toF : D.fibreProduct ⟶ D.F :=
  pullback.snd D.b D.a

/-- The canonical square of functors is a fibre product square. -/
public theorem isPullback : IsPullback D.toH D.toF D.b D.a :=
  IsPullback.of_hasPullback D.b D.a

end FppfFunctorPullbackSituation

end AlgebraicGeometry.Space

/-! ### Lifts into a pullback of types -/

namespace CategoryTheory.Limits.Types

variable {P P' H H' F F' G G' : Type v}

/-- The point of a pullback of types determined by a compatible pair of points. -/
public noncomputable def pullbackLiftPoint
    (pH : P ⟶ H) (pF : P ⟶ F) (b : H ⟶ G) (a : F ⟶ G)
    (hP : IsPullback pH pF b a) (y : H) (f : F) (hf : a f = b y) : P :=
  (exists_of_isPullback hP y f hf.symm).choose

/-- The first projection of the point of a pullback determined by a compatible pair is the
first member of the pair. -/
public theorem pullbackLiftPoint_fst
    (pH : P ⟶ H) (pF : P ⟶ F) (b : H ⟶ G) (a : F ⟶ G)
    (hP : IsPullback pH pF b a) (y : H) (f : F) (hf : a f = b y) :
    pH (pullbackLiftPoint pH pF b a hP y f hf) = y :=
  (exists_of_isPullback hP y f hf.symm).choose_spec.1

/-- The second projection of the point of a pullback determined by a compatible pair is the
second member of the pair. -/
public theorem pullbackLiftPoint_snd
    (pH : P ⟶ H) (pF : P ⟶ F) (b : H ⟶ G) (a : F ⟶ G)
    (hP : IsPullback pH pF b a) (y : H) (f : F) (hf : a f = b y) :
    pF (pullbackLiftPoint pH pF b a hP y f hf) = f :=
  (exists_of_isPullback hP y f hf.symm).choose_spec.2

/-- The two projections of a point of a pullback of types have the same image in the
common target. -/
public theorem pullback_comm_apply
    (pH : P ⟶ H) (pF : P ⟶ F) (b : H ⟶ G) (a : F ⟶ G)
    (hP : IsPullback pH pF b a) (z : P) : a (pF z) = b (pH z) :=
  (ConcreteCategory.congr_hom hP.w z).symm

/-- Lifts of a point of a pullback of types along a morphism of pullback squares correspond
to compatible lifts of its second component. -/
public noncomputable def pullbackLiftEquiv
    (pH : P ⟶ H) (pF : P ⟶ F) (b : H ⟶ G) (a : F ⟶ G)
    (pH' : P' ⟶ H') (pF' : P' ⟶ F') (b' : H' ⟶ G') (a' : F' ⟶ G')
    (hP : IsPullback pH pF b a) (hP' : IsPullback pH' pF' b' a')
    (rP : P' ⟶ P) (rH : H' ⟶ H) (rF : F' ⟶ F)
    (hrPH : ∀ z, pH (rP z) = rH (pH' z))
    (hrPF : ∀ z, pF (rP z) = rF (pF' z))
    (x : P) (y : H') (hxy : pH x = rH y) :
    {z : P' // rP z = x ∧ pH' z = y} ≃
      {f : F' // rF f = pF x ∧ a' f = b' y} where
  toFun z :=
    ⟨pF' z.1, by rw [← hrPF z.1, z.2.1],
      by rw [pullback_comm_apply pH' pF' b' a' hP' z.1, z.2.2]⟩
  invFun f :=
    ⟨pullbackLiftPoint pH' pF' b' a' hP' y f.1 f.2.2,
      ext_of_isPullback hP
        (by rw [hrPH, pullbackLiftPoint_fst, hxy])
        (by rw [hrPF, pullbackLiftPoint_snd]; exact f.2.1),
      pullbackLiftPoint_fst pH' pF' b' a' hP' y f.1 f.2.2⟩
  left_inv z :=
    have hc : a' (pF' z.1) = b' y :=
      (pullback_comm_apply pH' pF' b' a' hP' z.1).trans (congrArg b' z.2.2)
    Subtype.ext (ext_of_isPullback hP'
      ((pullbackLiftPoint_fst pH' pF' b' a' hP' y (pF' z.1) hc).trans z.2.2.symm)
      (pullbackLiftPoint_snd pH' pF' b' a' hP' y (pF' z.1) hc))
  right_inv f := Subtype.ext (pullbackLiftPoint_snd pH' pF' b' a' hP' y f.1 f.2.2)

end CategoryTheory.Limits.Types

/-! ### Lifts into a fibre product of fppf functors -/

namespace AlgebraicGeometry.Space

/-- Lifts of a fibre-product point over a prescribed point of `H` correspond
to compatible lifts of its `F` component. -/
public noncomputable def fibreProductLiftEquiv
    (D : FppfFunctorPullbackSituation.{u, v})
    (T T' : BigFppfOver D.B D.S D.hS)
    (i : T ⟶ T')
    (x : D.fibreProduct.obj (op T)) (y : D.H.obj (op T'))
    (hxy : D.toH.app (op T) x = D.H.map i.op y) :
    {z : D.fibreProduct.obj (op T') //
        (D.fibreProduct.map i.op z = x) ∧ (D.toH.app (op T') z = y)} ≃
      {f' : D.F.obj (op T') //
        (D.F.map i.op f' = D.toF.app (op T) x) ∧
          (D.a.app (op T') f' = D.b.app (op T') y)} := by
  let evT := (CategoryTheory.evaluation
    ((BigFppfOver D.B D.S D.hS)ᵒᵖ) (Type v)).obj (op T)
  let evT' := (CategoryTheory.evaluation
    ((BigFppfOver D.B D.S D.hS)ᵒᵖ) (Type v)).obj (op T')
  exact Types.pullbackLiftEquiv
    (evT.map D.toH) (evT.map D.toF) (evT.map D.b) (evT.map D.a)
    (evT'.map D.toH) (evT'.map D.toF) (evT'.map D.b) (evT'.map D.a)
    (D.isPullback.map evT) (D.isPullback.map evT')
    (D.fibreProduct.map i.op) (D.H.map i.op) (D.F.map i.op)
    (fun z => by simp [evT, evT'])
    (fun z => by simp [evT, evT'])
    x y hxy

/-- The forward map of the lift correspondence is the second fibre-product
projection. -/
public theorem fibreProductLiftEquiv_apply
    (D : FppfFunctorPullbackSituation.{u, v})
    (T T' : BigFppfOver D.B D.S D.hS)
    (i : T ⟶ T')
    (x : D.fibreProduct.obj (op T)) (y : D.H.obj (op T'))
    (hxy : D.toH.app (op T) x = D.H.map i.op y)
    (z : {z : D.fibreProduct.obj (op T') //
        (D.fibreProduct.map i.op z = x) ∧ (D.toH.app (op T') z = y)}) :
    ((fibreProductLiftEquiv D T T' i x y hxy) z).val =
      D.toF.app (op T') z.val := by rfl

/-- A fibre-product point over a point of `H` gives a commutative square for `a`. -/
private theorem app_toF_comm
    (D : FppfFunctorPullbackSituation.{u, v})
    (T T' : BigFppfOver D.B D.S D.hS) (i : T ⟶ T')
    (x : D.fibreProduct.obj (op T)) (y : D.H.obj (op T'))
    (hxy : D.toH.app (op T) x = D.H.map i.op y) :
    D.a.app (op T) (D.toF.app (op T) x) = D.G.map i.op (D.b.app (op T') y) := by
  simpa [hxy] using (congrArg (fun f => f.app (op T) x) D.isPullback.w).symm

/-! ### The three base-change statements -/

/-- **Stacks 049U, formal smoothness under base change.** -/
@[stacks 049U "formally_smooth_base_change", ega "IV 17.1.3" "(iii) smooth"]
public theorem FormallySmooth.baseChange
    (D : FppfFunctorPullbackSituation.{u, v})
    (ha : FormallySmooth D.a) :
    FormallySmooth D.toH := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨f', hf⟩ := ha T T' hT hT' i hi
    (D.toF.app (op T) x) (D.b.app (op T') y)
    (app_toF_comm D T T' i x y hxy)
  let z := (fibreProductLiftEquiv D T T' i x y hxy).symm ⟨f', hf⟩
  exact ⟨z.val, z.property⟩

/-- A base change of a formally étale transformation is formally étale. -/
@[stacks 049U "formally_etale_base_change", ega "IV 17.1.3" "(iii) étale"]
public theorem formallyEtale_baseChange
    (D : FppfFunctorPullbackSituation.{u, v})
    (ha : FormallyEtale D.a) :
    FormallyEtale D.toH := by
  intro T T' hT hT' i hi x y hxy
  apply (fibreProductLiftEquiv D T T' i x y hxy).existsUnique_subtype_congr.mpr
  exact ha T T' hT hT' i hi (D.toF.app (op T) x) (D.b.app (op T') y)
    (app_toF_comm D T T' i x y hxy)

/-- The base change of a formally unramified transformation is formally
unramified. -/
@[stacks 049U "formally_unramified_base_change", ega "IV 17.1.3" "(iii) unramified"]
public theorem formallyUnramified_baseChange
    (D : FppfFunctorPullbackSituation.{u, v})
    (ha : FormallyUnramified D.a) :
    FormallyUnramified D.toH := by
  intro T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂
  let e := fibreProductLiftEquiv D T T' i x y hxy
  let q₁ := (⟨z₁, hz₁⟩ : {z // IsLift D.toH i x y z})
  let q₂ := (⟨z₂, hz₂⟩ : {z // IsLift D.toH i x y z})
  exact congrArg Subtype.val (e.injective (Subtype.ext (ha T T' hT hT' i hi
    (D.toF.app (op T) x) (D.b.app (op T') y)
    (app_toF_comm D T T' i x y hxy) _ _ (e q₁).property (e q₂).property)))

end AlgebraicGeometry.Space

end
