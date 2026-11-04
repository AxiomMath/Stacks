module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GenericQuotientFlat
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensorTwoSided
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.RingTheory.GeometricallyIntegral.TFAE
public import StacksFrontier.RingTheory.GeometricallyIntegral.TensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The function field of a product of integral schemes over an algebraically closed field

Let `k` be an algebraically closed field and let `X`, `Y` be integral schemes over `Spec k`, with
fibre product `W = X ×_k Y` and projections `pr₁ : W ⟶ X`, `pr₂ : W ⟶ Y`.  Then `W` is integral,
`K(X) ⊗[k] K(Y)` is a domain, and **the function field of `W` is the fraction field of
`K(X) ⊗[k] K(Y)`**, the isomorphism sending `pr₁^* a · pr₂^* b` to `a ⊗ b`.  The isomorphism is
natural in dominant morphisms of the second factor.

## Main results

* `AlgebraicGeometry.IsIntegral.pullback_of_isAlgClosed`: `X ×_k Y` is integral (instance).
* `AlgebraicGeometry.isDomain_functionField_tensorProduct`: `K(X) ⊗[k] K(Y)` is a domain.
* `AlgebraicGeometry.isFractionRing_functionFieldTensorToPullback`: the map
  `K(X) ⊗[k] K(Y) → K(X ×_k Y)`, `a ⊗ b ↦ pr₁^* a · pr₂^* b`, is a fraction field.
* `AlgebraicGeometry.pullbackFunctionFieldEquiv`,
  `AlgebraicGeometry.pullbackFunctionFieldAlgEquiv`: the isomorphism
  `K(X ×_k Y) ≃ FractionRing (K(X) ⊗[k] K(Y))`, with
  `AlgebraicGeometry.pullbackFunctionFieldEquiv_mul`: it sends `pr₁^* a · pr₂^* b` to `a ⊗ b`.
* `AlgebraicGeometry.pullbackFunctionFieldEquiv_naturality`: compatibility with a dominant
  morphism `π : Y' ⟶ Y` over `k`, through `FractionRing` of `id ⊗ π^*`.

## Implementation notes

The `k`-algebra structure on a function field is `AlgebraicGeometry.stalkAlgebraOver` at the
generic point, the one in which
`AlgebraicGeometry.exists_isLocalization_atPrime_stalk_pullback_tensorProduct` is stated; it is not
an instance, so the statements carry it through `letI`.  The pullback `pr^*` of rational functions
along a dominant morphism is `AlgebraicGeometry.functionFieldMap` (the stalk map at the generic
point read through `stalkCongr`).  The projections are surjective, hence dominant, so they carry
the generic point of `W` to the generic points of `X` and `Y`.  At the generic point of `W` the
cited theorem presents `K(W)` as the localization of `K(X) ⊗[k] K(Y)` at the contraction of the
maximal ideal of the field `K(W)`, i.e. at the kernel of the canonical map; a localization of a
domain at a prime is injective, so the kernel is `⊥` and the localization is the fraction field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- The fibre product of two integral schemes over an algebraically closed field is integral. -/
instance IsIntegral.pullback_of_isAlgClosed [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] :
    IsIntegral (pullback f g) :=
  GenericQuotientFlat.isIntegral_pullback_of_isAlgClosed f g

/-- The tensor product over an algebraically closed field `k` of the function fields of two
integral `k`-schemes is a domain. -/
theorem isDomain_functionField_tensorProduct [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    IsDomain (X.functionField ⊗[k] Y.functionField) := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  have : Algebra.IsGeometricallyIntegral k Y.functionField := by
    let e : k ≃ₐ[k] AlgebraicClosure k :=
      AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    let φ : Y.functionField ⊗[k] AlgebraicClosure k ≃ₐ[k] Y.functionField :=
      (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans
        (Algebra.TensorProduct.rid k k Y.functionField)
    have : IsDomain (Y.functionField ⊗[k] AlgebraicClosure k) :=
      Function.Injective.isDomain φ.toRingHom φ.injective
    exact ((Algebra.isGeometricallyIntegral_tfae k Y.functionField).out 4 1).mp this
  exact Algebra.IsGeometricallyIntegral.isDomain_tensorProduct k _ _

/-- Two additive maps out of a tensor product that agree on pure tensors have equal underlying
functions. -/
private theorem tensorProduct_coe_ext {R A B S F G : Type*} [CommSemiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [AddCommMonoid S] [FunLike F (A ⊗[R] B) S]
    [FunLike G (A ⊗[R] B) S] [AddMonoidHomClass F (A ⊗[R] B) S] [AddMonoidHomClass G (A ⊗[R] B) S]
    (f : F) (g : G) (h : ∀ a b, f (a ⊗ₜ b) = g (a ⊗ₜ b)) : ⇑f = ⇑g := by
  funext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact h a b
  | add x y hx hy => simp only [map_add, hx, hy]

variable [IsIntegral X] [IsIntegral Y]

/-- The pullback of rational functions along a dominant morphism `h : Z ⟶ X` of integral
`k`-schemes is compatible with the `k`-algebra structures coming from the structure morphisms. -/
theorem functionFieldMap_stalkAlgebraOver_algebraMap {Z : Scheme.{u}} [IsIntegral Z] (h : Z ⟶ X)
    [IsDominant h] (s : Z ⟶ Spec (.of k)) (hs : h ≫ f = s) (r : k) :
    functionFieldMap h ((stalkAlgebraOver k f (genericPoint X)).algebraMap r) =
      (stalkAlgebraOver k s (genericPoint Z)).algebraMap r := by
  subst hs
  show ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ _ trivial ≫
    h.stalkMapOfEq _ _ (map_genericPoint_of_isDominant h)).hom r = _
  rw [Scheme.Hom.germ_stalkMapOfEq, ← Scheme.Hom.comp_appTop_assoc]
  rfl

/-- The pullback of rational functions along a dominant morphism `h : Z ⟶ X` of integral
`k`-schemes, as a map of `k`-algebras. -/
@[ega "I 8.2.7", ega "II 6.4.9" "partial"]
def functionFieldMapAlgHom {Z : Scheme.{u}} [IsIntegral Z] (h : Z ⟶ X) [IsDominant h]
    (s : Z ⟶ Spec (.of k)) (hs : h ≫ f = s) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k s (genericPoint Z)
    X.functionField →ₐ[k] Z.functionField :=
  letI := stalkAlgebraOver k f (genericPoint X)
  letI := stalkAlgebraOver k s (genericPoint Z)
  { toRingHom := functionFieldMap h
    commutes' := functionFieldMap_stalkAlgebraOver_algebraMap k f h s hs }

/-- The underlying map of `AlgebraicGeometry.functionFieldMapAlgHom` is
`AlgebraicGeometry.functionFieldMap`. -/
theorem functionFieldMapAlgHom_apply {Z : Scheme.{u}} [IsIntegral Z] (h : Z ⟶ X) [IsDominant h]
    (s : Z ⟶ Spec (.of k)) (hs : h ≫ f = s) (a : X.functionField) :
    functionFieldMapAlgHom k f h s hs a = functionFieldMap h a := rfl

variable [IsAlgClosed k]

/-- The canonical map `K(X) ⊗[k] K(Y) → K(X ×_k Y)`, `a ⊗ b ↦ pr₁^* a · pr₂^* b`. -/
def functionFieldTensorToPullback :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    X.functionField ⊗[k] Y.functionField →+* (pullback f g).functionField :=
  letI := stalkAlgebraOver k f (genericPoint X)
  letI := stalkAlgebraOver k g (genericPoint Y)
  letI := stalkAlgebraOver k (pullback.fst f g ≫ f) (genericPoint (pullback f g : Scheme.{u}))
  Algebra.TensorProduct.lift (functionFieldMapAlgHom k f (pullback.fst f g) _ rfl)
    (functionFieldMapAlgHom k g (pullback.snd f g) _ pullback.condition.symm)
    (fun _ _ => Commute.all _ _) |>.toRingHom

/-- `AlgebraicGeometry.functionFieldTensorToPullback` sends `a ⊗ b` to `pr₁^* a · pr₂^* b`. -/
theorem functionFieldTensorToPullback_tmul (a : X.functionField) (b : Y.functionField) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    functionFieldTensorToPullback k f g (a ⊗ₜ b) =
      functionFieldMap (pullback.fst f g) a * functionFieldMap (pullback.snd f g) b :=
  rfl


/-- **The function field of `X ×_k Y` is the fraction field of `K(X) ⊗[k] K(Y)`**, through the
canonical map `a ⊗ b ↦ pr₁^* a · pr₂^* b`. -/
theorem isFractionRing_functionFieldTensorToPullback :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    letI := (functionFieldTensorToPullback k f g).toAlgebra
    IsFractionRing (X.functionField ⊗[k] Y.functionField) (pullback f g).functionField := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  have hx : pullback.fst f g (genericPoint (pullback f g : Scheme.{u})) = genericPoint X :=
    map_genericPoint_of_isDominant _
  have hy : pullback.snd f g (genericPoint (pullback f g : Scheme.{u})) = genericPoint Y :=
    map_genericPoint_of_isDominant _
  obtain ⟨ψ₀, h₁, h₂, hloc₀⟩ :=
    exists_isLocalization_atPrime_stalk_pullback_tensorProduct k f g
      (genericPoint (pullback f g : Scheme.{u}))
  obtain ⟨ψ, hψ, hloc⟩ := exists_tensor_stalk_transport₂ k f g _ _ _ _ hx hy ψ₀ hloc₀
  have hψψ : ψ = (functionFieldTensorToPullback k f g) := by
    refine DFunLike.ext' (tensorProduct_coe_ext _ _ fun a b => ?_)
    rw [hψ, h₁, h₂]
    rfl
  subst hψψ
  let := (functionFieldTensorToPullback k f g).toAlgebra
  have := isDomain_functionField_tensorProduct k f g
  have hinj : Function.Injective (functionFieldTensorToPullback k f g) :=
    IsLocalization.injective (M := (Ideal.comap (functionFieldTensorToPullback k f g)
      (IsLocalRing.maximalIdeal (pullback f g).functionField)).primeCompl)
      (pullback f g).functionField (Ideal.primeCompl_le_nonZeroDivisors _)
  have hP : Ideal.comap (functionFieldTensorToPullback k f g)
      (IsLocalRing.maximalIdeal (pullback f g).functionField) = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hM : (Ideal.comap (functionFieldTensorToPullback k f g)
      (IsLocalRing.maximalIdeal (pullback f g).functionField)).primeCompl =
      nonZeroDivisors (X.functionField ⊗[k] Y.functionField) := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, hP, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
  rw [IsLocalization.AtPrime, hM] at hloc
  exact hloc


/-- **The function field of a product.**  For integral schemes `X`, `Y` over an algebraically
closed field `k`, the function field of `X ×_k Y` is isomorphic to the fraction field of
`K(X) ⊗[k] K(Y)`. -/
def pullbackFunctionFieldEquiv :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    (pullback f g).functionField ≃+* FractionRing (X.functionField ⊗[k] Y.functionField) :=
  letI := stalkAlgebraOver k f (genericPoint X)
  letI := stalkAlgebraOver k g (genericPoint Y)
  letI := (functionFieldTensorToPullback k f g).toAlgebra
  haveI := isFractionRing_functionFieldTensorToPullback k f g
  (IsLocalization.algEquiv (nonZeroDivisors (X.functionField ⊗[k] Y.functionField))
    (pullback f g).functionField (FractionRing (X.functionField ⊗[k] Y.functionField))).toRingEquiv

/-- `AlgebraicGeometry.pullbackFunctionFieldEquiv` is compatible with the canonical maps out of
`K(X) ⊗[k] K(Y)`. -/
theorem pullbackFunctionFieldEquiv_functionFieldTensorToPullback
    (z : letI := stalkAlgebraOver k f (genericPoint X)
      letI := stalkAlgebraOver k g (genericPoint Y)
      X.functionField ⊗[k] Y.functionField) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    pullbackFunctionFieldEquiv k f g (functionFieldTensorToPullback k f g z) =
      algebraMap _ (FractionRing (X.functionField ⊗[k] Y.functionField)) z :=
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  let := (functionFieldTensorToPullback k f g).toAlgebra
  have := isFractionRing_functionFieldTensorToPullback k f g
  (IsLocalization.algEquiv (nonZeroDivisors (X.functionField ⊗[k] Y.functionField))
    (pullback f g).functionField (FractionRing (X.functionField ⊗[k] Y.functionField))).commutes z

/-- `AlgebraicGeometry.pullbackFunctionFieldEquiv` sends `pr₁^* a · pr₂^* b` to `a ⊗ b`. -/
theorem pullbackFunctionFieldEquiv_mul (a : X.functionField) (b : Y.functionField) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    pullbackFunctionFieldEquiv k f g
        (functionFieldMap (pullback.fst f g) a * functionFieldMap (pullback.snd f g) b) =
      algebraMap (X.functionField ⊗[k] Y.functionField) (FractionRing _) (a ⊗ₜ b) :=
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  pullbackFunctionFieldEquiv_functionFieldTensorToPullback k f g (a ⊗ₜ b)

/-- `AlgebraicGeometry.pullbackFunctionFieldEquiv` is `k`-linear: it carries the image of `k` in
`K(X ×_k Y)` (through `pr₁ ≫ f`) to the image of `k` in the fraction field. -/
theorem pullbackFunctionFieldEquiv_algebraMap (r : k) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    pullbackFunctionFieldEquiv k f g
        ((stalkAlgebraOver k (pullback.fst f g ≫ f)
          (genericPoint (pullback f g : Scheme.{u}))).algebraMap r) =
      algebraMap _ (FractionRing (X.functionField ⊗[k] Y.functionField))
        (algebraMap k (X.functionField ⊗[k] Y.functionField) r) := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  rw [← functionFieldMap_stalkAlgebraOver_algebraMap k f (pullback.fst f g) _ rfl,
    ← mul_one (functionFieldMap _ _), ← map_one (functionFieldMap (pullback.snd f g)),
    pullbackFunctionFieldEquiv_mul, Algebra.TensorProduct.algebraMap_apply]


/-- `AlgebraicGeometry.pullbackFunctionFieldEquiv` as an isomorphism of `k`-algebras, the
`k`-algebra structure on `K(X ×_k Y)` coming from `pr₁ ≫ f`. -/
def pullbackFunctionFieldAlgEquiv :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    letI := stalkAlgebraOver k (pullback.fst f g ≫ f) (genericPoint (pullback f g : Scheme.{u}))
    (pullback f g).functionField ≃ₐ[k] FractionRing (X.functionField ⊗[k] Y.functionField) :=
  letI := stalkAlgebraOver k f (genericPoint X)
  letI := stalkAlgebraOver k g (genericPoint Y)
  letI := stalkAlgebraOver k (pullback.fst f g ≫ f) (genericPoint (pullback f g : Scheme.{u}))
  AlgEquiv.ofRingEquiv (f := pullbackFunctionFieldEquiv k f g) fun r => by
    rw [pullbackFunctionFieldEquiv_algebraMap]
    exact (IsScalarTower.algebraMap_apply k (X.functionField ⊗[k] Y.functionField) _ r).symm

/-- The underlying map of `AlgebraicGeometry.pullbackFunctionFieldAlgEquiv` is
`AlgebraicGeometry.pullbackFunctionFieldEquiv`. -/
theorem pullbackFunctionFieldAlgEquiv_apply (z : (pullback f g).functionField) :
    pullbackFunctionFieldAlgEquiv k f g z = pullbackFunctionFieldEquiv k f g z :=
  rfl

section Naturality

variable {Y' : Scheme.{u}} [IsIntegral Y'] (g' : Y' ⟶ Spec (.of k)) (π : Y' ⟶ Y) (hπ : π ≫ g = g')

omit [IsIntegral X] [IsIntegral Y] [IsAlgClosed k] [IsIntegral Y'] in
/-- For a dominant morphism `π : Y' ⟶ Y` over `k`, the morphism `1 × π : X ×_k Y' ⟶ X ×_k Y` is
dominant: its range is the preimage of the range of `π` under the open map `pr₂`. -/
theorem isDominant_pullback_map_id [IsDominant π] :
    IsDominant (pullback.map f g' f g (𝟙 X) π (𝟙 _) (by simp) (by simp [hπ])) := by
  have := universallyOpen_of_field k f
  have : UniversallyOpen (pullback.snd f g) := inferInstance
  have hopen : IsOpenMap (pullback.snd f g) := (pullback.snd f g).isOpenMap
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_map]
  simpa using Dense.preimage (IsDominant.denseRange (f := π)) hopen

omit [IsAlgClosed k] in
/-- For a dominant morphism `π : Y' ⟶ Y` of integral `k`-schemes, `id ⊗ π^*` is injective. -/
theorem injective_tensorProductMap_functionFieldMapAlgHom [IsDominant π] :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    letI := stalkAlgebraOver k g' (genericPoint Y')
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k X.functionField)
      (functionFieldMapAlgHom k g π g' hπ)) := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  let := stalkAlgebraOver k g' (genericPoint Y')
  convert Module.Flat.lTensor_preserves_injective_linearMap
    (functionFieldMapAlgHom k g π g' hπ).toLinearMap
    (functionFieldMapAlgHom k g π g' hπ).toRingHom.injective using 1
  · exact tensorProduct_coe_ext _ _ fun _ _ => rfl
  · infer_instance

/-- **Naturality of the function field of a product in the second factor.**  For a dominant
morphism `π : Y' ⟶ Y` of integral `k`-schemes, the isomorphisms
`AlgebraicGeometry.pullbackFunctionFieldEquiv` intertwine the pullback along `1 × π` with the map
of fraction fields induced by `id ⊗ π^*`. -/
theorem pullbackFunctionFieldEquiv_naturality [IsDominant π] (z : (pullback f g).functionField) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    letI := stalkAlgebraOver k g' (genericPoint Y')
    haveI := isDominant_pullback_map_id k f g g' π hπ
    haveI := isDomain_functionField_tensorProduct k f g'
    pullbackFunctionFieldEquiv k f g'
        (functionFieldMap (pullback.map f g' f g (𝟙 X) π (𝟙 _) (by simp) (by simp [hπ])) z) =
      IsFractionRing.map (K := FractionRing (X.functionField ⊗[k] Y.functionField))
        (L := FractionRing (X.functionField ⊗[k] Y'.functionField))
        (injective_tensorProductMap_functionFieldMapAlgHom k f g g' π hπ)
        (pullbackFunctionFieldEquiv k f g z) := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  let := stalkAlgebraOver k g' (genericPoint Y')
  let m := pullback.map f g' f g (𝟙 X) π (𝟙 _) (by simp) (by simp [hπ])
  have : IsDominant m := isDominant_pullback_map_id k f g g' π hπ
  have := isDomain_functionField_tensorProduct k f g
  have := isDomain_functionField_tensorProduct k f g'
  have hm₁ : m ≫ pullback.fst f g = pullback.fst f g' :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hm₂ : m ≫ pullback.snd f g = pullback.snd f g' ≫ π := pullback.lift_snd _ _ _
  -- functoriality of the maps of function fields
  have hcomp : ∀ {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B] [IsIntegral C]
      (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] (c : A ⟶ C) [IsDominant c]
      (_ : a ≫ b = c) (t : C.functionField),
      functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
    intro A B C _ _ _ a b _ _ c _ hc t
    subst hc
    have := Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A) (genericPoint B) (genericPoint C)
      (map_genericPoint_of_isDominant a) (map_genericPoint_of_isDominant b)
      (map_genericPoint_of_isDominant (a ≫ b))
    exact (congrArg (fun φ => φ.hom t) this).symm
  have h₁ : ∀ a, functionFieldMap m (functionFieldMap (pullback.fst f g) a) =
      functionFieldMap (pullback.fst f g') a := hcomp _ _ _ hm₁
  have h₂ : ∀ b, functionFieldMap m (functionFieldMap (pullback.snd f g) b) =
      functionFieldMap (pullback.snd f g') (functionFieldMap π b) := fun b =>
    (hcomp m (pullback.snd f g) (pullback.snd f g' ≫ π) hm₂ b).trans
      (hcomp (pullback.snd f g') π _ rfl b).symm
  suffices H : ((pullbackFunctionFieldEquiv k f g').toRingHom.comp (functionFieldMap m)).comp
      (functionFieldTensorToPullback k f g) =
      ((IsFractionRing.map (K := FractionRing (X.functionField ⊗[k] Y.functionField))
        (L := FractionRing (X.functionField ⊗[k] Y'.functionField))
        (injective_tensorProductMap_functionFieldMapAlgHom k f g g' π hπ)).comp
          (pullbackFunctionFieldEquiv k f g).toRingHom).comp
        (functionFieldTensorToPullback k f g) by
    let := (functionFieldTensorToPullback k f g).toAlgebra
    have := isFractionRing_functionFieldTensorToPullback k f g
    exact DFunLike.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors _) H) z
  refine DFunLike.ext' (tensorProduct_coe_ext _ _ fun a b => ?_)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [functionFieldTensorToPullback_tmul, map_mul, h₁, h₂, pullbackFunctionFieldEquiv_mul,
    pullbackFunctionFieldEquiv_mul, IsFractionRing.map,
    IsLocalization.map_eq]
  rfl

end Naturality

end AlgebraicGeometry

end
