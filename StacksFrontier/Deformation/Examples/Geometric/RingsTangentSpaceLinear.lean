module

public import StacksFrontier.Algebra.Category.FGModuleCat.TensorFunctor
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceFinite
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceIdentification

/-!
# The receptacle functor `V ↦ Ext¹_P(NL_{P/k}, P ⊗[k] V)`, linearly

Let `k` be a field and `P` a `k`-algebra. Tensoring the coefficients of the first Ext group of
the naive cotangent complex of `P` over `k` gives a functor

`FGModuleCat k ⥤ ModuleCat k`,  `V ↦ Ext¹_P(NL_{P/k}, P ⊗[k] V)`,

and this file proves that it is additive and `k`-linear.

That is the hypothesis which
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` asks of a receptacle
for the tangent space of a predeformation category, and it is the one point at which a merely
additive comparison is not enough: the canonical vector-space structure of **Stacks 06IH** on
the tangent space is defined through the whole functor `V ↦ 𝓕(k[V])`, so linearity of a map out
of it is available only from naturality against an honestly `k`-linear receptacle, and
finite-dimensionality over a field does not transport along an additive equivalence.

Linearity comes from `Stacks.Deformation.extCokernelLinearIso`, the `B`-linear form of the
Ext--cokernel comparison: the map induced on first Ext by a coefficient map is that comparison
conjugating postcomposition on conormal functionals, and postcomposition is linear in the
coefficient map.

## Main definitions

* `Stacks.Deformation.naiveCotangentExtOneLinearMap`: the map
  `Ext¹_B(NL_{B/A}, M) →ₗ[B] Ext¹_B(NL_{B/A}, N)` induced by a coefficient map, as a `B`-linear
  map rather than only an additive one.
* `Deformation.Examples.naiveCotangentExtOneTensorFunctor`: the functor
  `V ↦ Ext¹_P(NL_{P/k}, P ⊗[k] V)`.

## Main results

* `Stacks.Deformation.naiveCotangentExtOneMap_smul`: the map induced on first Ext is `B`-linear
  in the coefficient map.
* `Deformation.Examples.naiveCotangentExtOneTensorFunctor_additive` and
  `Deformation.Examples.naiveCotangentExtOneTensorFunctor_linear`: the receptacle functor is
  additive and `k`-linear.
* `Deformation.Examples.finiteDimensional_naiveCotangentExtOneTensorFunctor_obj_rankOne`:
  **Stacks 0DY4(2)** for the value of the receptacle at the rank-one module, transported from
  `Deformation.Examples.finiteDimensional_naiveCotangentExtOne` along `P ⊗[k] k ≅ P`.

## Implementation notes

The `k`-module structure used on the Ext groups is the restriction of scalars along
`algebraMap k P` of the canonical `P`-module structure, which is the structure
`Deformation.Examples.finiteDimensional_naiveCotangentExtOne_compHom` is stated for. It is
installed as a `local instance` rather than taken as a hypothesis because the functor below
must bundle it uniformly in `V`. The alternative, the `k`-module structure coming from
`CategoryTheory.Linear k (ModuleCat P)`, would make the Ext groups `k`-modules without
mentioning `P`, but relating its scalar action to the `P`-action means unfolding the derived
category's localization-transported linear structure, which the restriction of scalars avoids.

`Stacks.Deformation.conormalCokernelPushLinear` restates
`Stacks.Deformation.conormalCokernelPush` of
`StacksFrontier/Deformation/SquareZero/AlgebraExtensionMaps.lean` as the `B`-linear map it is
built from; the two agree by `rfl`, and the restatement is what carries the scalar action
through the Ext--cokernel comparison.

## References

* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
* [Stacks Project, Tag 0DY4](https://stacks.math.columbia.edu/tag/0DY4)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u₂ u₃ uM uN w

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

section CoefficientLinearity

variable (A : Type u₂) (B : Type u₃) [CommRing A] [CommRing B] [Algebra A B]
  {L : Type uM} [AddCommGroup L] [Module B L]
  {M : Type uM} [AddCommGroup M] [Module B M]
  {N : Type uN} [AddCommGroup N] [Module B N]

/-- Postcomposition with a coefficient map on conormal cokernels, as a `B`-linear map, whose
underlying additive map is `conormalCokernelPush`. -/
public def conormalCokernelPushLinear (c : M →ₗ[B] N) :
    extOneCokernel A B M →ₗ[B] extOneCokernel A B N :=
  Submodule.mapQ _ _ (towerConormalPush A B c) (by
    rintro δ ⟨t, rfl⟩
    exact ⟨c.comp t, rfl⟩)

/-- The additive map on conormal cokernels is the underlying additive map of the linear one. -/
public lemma conormalCokernelPush_eq (c : M →ₗ[B] N) :
    conormalCokernelPush A B c = (conormalCokernelPushLinear A B c).toAddMonoidHom := rfl

/-- Postcomposition on conormal cokernels is additive in the coefficient map. -/
public lemma conormalCokernelPush_add (c d : M →ₗ[B] N) (y : extOneCokernel A B M) :
    conormalCokernelPush A B (c + d) y
      = conormalCokernelPush A B c y + conormalCokernelPush A B d y := by
  induction y using Quotient.inductionOn' with
  | h δ => rfl

/-- Postcomposition on conormal cokernels is `B`-linear in the coefficient map. -/
public lemma conormalCokernelPush_smul (b : B) (c : M →ₗ[B] N) (y : extOneCokernel A B M) :
    conormalCokernelPush A B (b • c) y = b • conormalCokernelPush A B c y := by
  induction y using Quotient.inductionOn' with
  | h δ => rfl

/-- **The map induced on first Ext is additive in the coefficient map.** -/
public lemma naiveCotangentExtOneMap_add (c d : M →ₗ[B] N) (x : naiveCotangentExtOne A B M) :
    naiveCotangentExtOneMap A B (c + d) x
      = naiveCotangentExtOneMap A B c x + naiveCotangentExtOneMap A B d x := by
  show (extCokernelIso A B N).symm (conormalCokernelPush A B (c + d)
      (extCokernelIso A B M x)) = _
  rw [conormalCokernelPush_add]
  exact map_add (extCokernelIso A B N).symm _ _

/-- **The map induced on first Ext is `B`-linear in the coefficient map**, that is,
`Ext¹_B(NL_{B/A}, -)` is a `B`-linear functor of its coefficient module and not merely an
additive one.

It rests on `extCokernelLinearIso`. For `A = k` a field, `B = P` and the coefficient module
`P ⊗[k] V` it is the `k`-linearity of `naiveCotangentExtOneTensorFunctor`, which is what the
finite-dimensionality criterion for a tangent space consumes. -/
public lemma naiveCotangentExtOneMap_smul (b : B) (c : M →ₗ[B] N)
    (x : naiveCotangentExtOne A B M) :
    naiveCotangentExtOneMap A B (b • c) x = b • naiveCotangentExtOneMap A B c x := by
  show (extCokernelLinearIso A B N).symm (conormalCokernelPush A B (b • c)
      (extCokernelIso A B M x)) =
    b • (extCokernelLinearIso A B N).symm (conormalCokernelPush A B c (extCokernelIso A B M x))
  rw [conormalCokernelPush_smul, map_smul]

/-- The map `Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)` induced by a coefficient map
`c : M → N`, as a `B`-linear map. Its underlying function is
`Stacks.Deformation.naiveCotangentExtOneMap`. -/
public def naiveCotangentExtOneLinearMap (c : M →ₗ[B] N) :
    naiveCotangentExtOne A B M →ₗ[B] naiveCotangentExtOne A B N where
  toFun := naiveCotangentExtOneMap A B c
  map_add' := map_add (naiveCotangentExtOneMap A B c)
  map_smul' b x := by
    change (extCokernelLinearIso A B N).symm (conormalCokernelPushLinear A B c
        (extCokernelLinearIso A B M (b • x))) =
      b • (extCokernelLinearIso A B N).symm (conormalCokernelPushLinear A B c
        (extCokernelLinearIso A B M x))
    rw [map_smul, map_smul, map_smul]

/-- The linear map `naiveCotangentExtOneLinearMap A B c` acts as
`naiveCotangentExtOneMap A B c`. -/
@[simp]
public lemma naiveCotangentExtOneLinearMap_apply (c : M →ₗ[B] N)
    (x : naiveCotangentExtOne A B M) :
    naiveCotangentExtOneLinearMap A B c x = naiveCotangentExtOneMap A B c x := rfl

end CoefficientLinearity

section CoefficientCongr

variable (A B : Type w) [CommRing A] [CommRing B] [Algebra A B]
  {M N : Type w} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- A linear equivalence of coefficient modules induces a linear equivalence of the first Ext
groups of the naive cotangent complex. -/
public def naiveCotangentExtOneCongr (e : M ≃ₗ[B] N) :
    naiveCotangentExtOne A B M ≃ₗ[B] naiveCotangentExtOne A B N where
  __ := naiveCotangentExtOneLinearMap A B (e : M →ₗ[B] N)
  invFun := naiveCotangentExtOneLinearMap A B (e.symm : N →ₗ[B] M)
  left_inv x := by
    change naiveCotangentExtOneMap A B (e.symm : N →ₗ[B] M)
      (naiveCotangentExtOneMap A B (e : M →ₗ[B] N) x) = x
    rw [← naiveCotangentExtOneMap_comp]
    have h : ((e.symm : N →ₗ[B] M).comp (e : M →ₗ[B] N)) = LinearMap.id := by
      ext y; simp
    rw [h, naiveCotangentExtOneMap_id]
  right_inv x := by
    change naiveCotangentExtOneMap A B (e : M →ₗ[B] N)
      (naiveCotangentExtOneMap A B (e.symm : N →ₗ[B] M) x) = x
    rw [← naiveCotangentExtOneMap_comp]
    have h : ((e : M →ₗ[B] N).comp (e.symm : N →ₗ[B] M)) = LinearMap.id := by
      ext y; simp
    rw [h, naiveCotangentExtOneMap_id]

end CoefficientCongr

end Stacks.Deformation

namespace Deformation.Examples

open Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

/-- The `k`-module structure on a first Ext group of the naive cotangent complex of `P` over
`k` is the restriction of scalars along `algebraMap k P`. -/
local instance moduleBaseNaiveCotangentExtOne {k P : Type w} [Field k] [CommRing P]
    [Algebra k P] {N : Type w} [AddCommGroup N] [Module P N] :
    Module k (naiveCotangentExtOne k P N) :=
  Module.compHom _ (algebraMap k P)

/-- The scalar actions of `k` and `P` on a first Ext group of the naive cotangent complex of `P`
over `k` form a scalar tower. -/
local instance isScalarTowerBaseNaiveCotangentExtOne {k P : Type w} [Field k] [CommRing P]
    [Algebra k P] {N : Type w} [AddCommGroup N] [Module P N] :
    IsScalarTower k P (naiveCotangentExtOne k P N) :=
  ⟨fun a b x => by
    rw [Algebra.smul_def]
    exact mul_smul (algebraMap k P a) b x⟩

section Functor

variable (k P : Type w) [Field k] [CommRing P] [Algebra k P]
  {V V' V'' : Type w} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V''] [Module k V'']

/-- The coefficient map induced by the identity is the identity. -/
public lemma tensorRightMap_eq_id :
    tensorRightMap (k := k) P (LinearMap.id : V →ₗ[k] V) = LinearMap.id :=
  LinearMap.ext fun x => tensorRightMap_id P x

/-- The coefficient map induced by a composite is the composite of the coefficient maps. -/
public lemma tensorRightMap_comp (f : V →ₗ[k] V') (g : V' →ₗ[k] V'') :
    tensorRightMap (k := k) P (g.comp f)
      = (tensorRightMap P g).comp (tensorRightMap P f) := by
  simp [tensorRightMap, ← TensorProduct.AlgebraTensorModule.map_comp]

/-- The coefficient map is additive in the inducing `k`-linear map. -/
public lemma tensorRightMap_add (f g : V →ₗ[k] V') :
    tensorRightMap (k := k) P (f + g) = tensorRightMap P f + tensorRightMap P g :=
  TensorProduct.AlgebraTensorModule.map_add_right _ _ _

/-- The coefficient map is `k`-linear in the inducing `k`-linear map, the scalar acting on the
target through `algebraMap k P`. -/
public lemma tensorRightMap_smul (a : k) (f : V →ₗ[k] V') :
    tensorRightMap (k := k) P (a • f) = algebraMap k P a • tensorRightMap P f := by
  refine LinearMap.ext fun x => ?_
  induction x with
  | zero => simp
  | tmul p v =>
      show p ⊗ₜ[k] (a • f v) = algebraMap k P a • (p ⊗ₜ[k] f v)
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, ← smul_eq_mul,
        TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

/-- **The receptacle `V ↦ Ext¹_P(NL_{P/k}, P ⊗[k] V)`.**  A finitely generated `k`-vector space
`V` is sent to the first Ext group of the naive cotangent complex of `P` over `k` with
coefficients in `P ⊗[k] V`, regarded as a `k`-vector space by restriction of scalars, and a
`k`-linear map `V → V'` acts through the coefficient map `P ⊗[k] V → P ⊗[k] V'`.

This is the functor against which the extension class of a first-order deformation of `P` is
natural, so it is the receptacle that
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` consumes for the
tangent space of the deformation category of `P`. -/
public def naiveCotangentExtOneTensorFunctor : FGModuleCat.{w} k ⥤ ModuleCat.{w + 1} k where
  obj V := ModuleCat.of k (naiveCotangentExtOne k P (P ⊗[k] V.obj))
  map f := ModuleCat.ofHom
    ((naiveCotangentExtOneLinearMap k P (tensorRightMap P f.hom.hom)).restrictScalars k)
  map_id V := by
    ext x
    change naiveCotangentExtOneMap k P (tensorRightMap P (LinearMap.id : V.obj →ₗ[k] V.obj)) x
      = x
    rw [tensorRightMap_eq_id, naiveCotangentExtOneMap_id]
  map_comp f g := by
    ext x
    change naiveCotangentExtOneMap k P (tensorRightMap P (g.hom.hom.comp f.hom.hom)) x = _
    rw [tensorRightMap_comp, naiveCotangentExtOneMap_comp]
    rfl

/-- The functor `naiveCotangentExtOneTensorFunctor k P` sends `V` to
`Ext¹_P(NL_{P/k}, P ⊗[k] V)`. -/
@[simp]
public lemma naiveCotangentExtOneTensorFunctor_obj (V : FGModuleCat.{w} k) :
    (naiveCotangentExtOneTensorFunctor k P).obj V
      = ModuleCat.of k (naiveCotangentExtOne k P (P ⊗[k] V.obj)) := rfl

/-- The functor `naiveCotangentExtOneTensorFunctor k P` sends a morphism `f` to the map induced
by the coefficient map `tensorRightMap P f`. -/
@[simp]
public lemma naiveCotangentExtOneTensorFunctor_map_apply {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
    (x : naiveCotangentExtOne k P (P ⊗[k] V.obj)) :
    (naiveCotangentExtOneTensorFunctor k P).map f x
      = naiveCotangentExtOneMap k P (tensorRightMap P f.hom.hom) x := rfl

/-- The receptacle functor is additive. -/
public instance naiveCotangentExtOneTensorFunctor_additive :
    (naiveCotangentExtOneTensorFunctor k P).Additive where
  map_add {V V'} f g := by
    ext x
    change naiveCotangentExtOneMap k P (tensorRightMap P (f.hom.hom + g.hom.hom)) x
      = naiveCotangentExtOneMap k P (tensorRightMap P f.hom.hom) x
        + naiveCotangentExtOneMap k P (tensorRightMap P g.hom.hom) x
    rw [tensorRightMap_add]
    exact naiveCotangentExtOneMap_add k P _ _ x

/-- **The receptacle functor is `k`-linear.**  This is the hypothesis of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` that cannot be
weakened: a finite-dimensionality transported along an additive equivalence is not
finite-dimensionality over `k`. -/
public instance naiveCotangentExtOneTensorFunctor_linear :
    (naiveCotangentExtOneTensorFunctor k P).Linear k where
  map_smul {V V'} f a := by
    ext x
    change naiveCotangentExtOneMap k P (tensorRightMap P (a • f.hom.hom)) x
      = a • naiveCotangentExtOneMap k P (tensorRightMap P f.hom.hom) x
    rw [tensorRightMap_smul]
    exact naiveCotangentExtOneMap_smul k P (algebraMap k P a) _ x

/-- The value of the receptacle at the rank-one module is the first Ext group with coefficients
in `P` itself, `Ext¹_P(NL_{P/k}, P)`, through `P ⊗[k] k ≅ P`. -/
public def naiveCotangentExtOneTensorFunctorObjRankOne :
    naiveCotangentExtOne k P (P ⊗[k] (FGModuleCat.of k k).obj)
      ≃ₗ[P] naiveCotangentExtOne k P P :=
  naiveCotangentExtOneCongr k P (TensorProduct.AlgebraTensorModule.rid k P P)

/-- **Stacks 0DY4(2)** for the value of the receptacle at the rank-one module. Let `k` be a
field and `P` a `k`-algebra of finite type which is smooth over `k` outside a finite set of
primes. Then `Ext¹_P(NL_{P/k}, P ⊗[k] k)` is a finite-dimensional `k`-vector space.

This is `Deformation.Examples.finiteDimensional_naiveCotangentExtOne` transported along
`P ⊗[k] k ≅ P`; the transport is `P`-linear, hence `k`-linear for the restricted scalars, which
is why it carries finite-dimensionality. -/
public theorem finiteDimensional_naiveCotangentExtOneTensorFunctor_obj_rankOne
    [Algebra.FiniteType k P]
    (hfinite : {q : PrimeSpectrum P | ¬ Algebra.IsSmoothAt k q.asIdeal}.Finite) :
    FiniteDimensional k ((naiveCotangentExtOneTensorFunctor k P).obj (FGModuleCat.of k k)) := by
  have : FiniteDimensional k (naiveCotangentExtOne k P P) :=
    finiteDimensional_naiveCotangentExtOne k P hfinite
  exact ((naiveCotangentExtOneTensorFunctorObjRankOne k P).symm.restrictScalars k).finiteDimensional

end Functor

end Deformation.Examples

end
