/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.LeftInvariantModel
public import StacksFrontier.FieldTheory.RationalGroupApproximation

/-!
# The rational group of an integral group scheme

Let `G` be an integral group scheme over an algebraically closed field `k`, with function field
`K = K(G)`.  The morphism `(x, g) ↦ g x` of `G × G` to `G` is dominant, so it induces
`Δ : K → K(G × G) ≅ Frac(K ⊗[k] K)` (`AlgebraicGeometry.GenericQuotientFlat.functionFieldComul`),
the *rational group* of `G` in Perrin's sense.  Associativity of the multiplication of `G`
makes `Δ` coassociative in the form `(Δ ⊗ 1)~ ∘ Δ = (1 ⊗ Δ)~ ∘ Δ` of
`TensorProduct.RationalGroup.exists_fg_leftInvariant_intermediateField`
(`AlgebraicGeometry.GenericQuotientFlat.functionFieldComul_coassoc`), so every finite set of
rational functions on `G` lies in a finitely generated left-invariant subfield of `K`
(`AlgebraicGeometry.GenericQuotientFlat.exists_fg_leftInvariant_functionField`).

This is a step of the proof that a group scheme over a field of characteristic zero is reduced
(Stacks, Remark 047O), following Perrin's thesis (III 2.2.1).

## Main results

* `AlgebraicGeometry.functionFieldMap_comp_apply`: functoriality of the pullback of rational
  functions along dominant morphisms.
* `AlgebraicGeometry.functionField_pullback_ringHom_ext`: ring maps out of `K(X ×_k Y)` agree once
  they agree on `pr₁^* K(X)` and on `pr₂^* K(Y)`.
* `AlgebraicGeometry.GenericQuotientFlat.functionFieldComul`, `functionFieldComul_coassoc`,
  `exists_fg_leftInvariant_functionField`.

## Implementation notes

The triple product is `(G ⊗ G) ⊗ G`; its function field is mapped to
`Frac(Frac(K ⊗[k] K) ⊗[k] K)` by `AlgebraicGeometry.GenericQuotientFlat.cubeMap`, the
composite of `AlgebraicGeometry.pullbackFunctionFieldEquiv` twice.  The two sides of
coassociativity are the pullbacks along `((x, g), h) ↦ (g x, h)` and `((x, g), h) ↦ (x, h g)`,
followed by `(x, g) ↦ g x`; these composites agree by associativity, and the identification of
each pullback with the corresponding algebraic map is checked on `pr₁^*` and `pr₂^*` by
`AlgebraicGeometry.functionField_pullback_ringHom_ext`.  All the morphisms have sections, hence
are surjective and dominant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- **Functoriality of the pullback of rational functions** along dominant morphisms of integral
schemes. -/
theorem functionFieldMap_comp_apply {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  exact (congrArg (fun φ => φ.hom t) (Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A)
    (genericPoint B) (genericPoint C) (map_genericPoint_of_isDominant a)
    (map_genericPoint_of_isDominant b) (map_genericPoint_of_isDominant (a ≫ b)))).symm

/-- A morphism of schemes with a section is dominant. -/
theorem isDominant_of_comp_eq_id {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) (h : s ≫ f = 𝟙 Y) :
    IsDominant f := by
  have : Surjective f := ⟨fun y => ⟨s y, by rw [← Scheme.Hom.comp_apply, h]; rfl⟩⟩
  infer_instance

section PullbackExt

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (g : Y ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y]

/-- **Ring maps out of the function field of a product** over an algebraically closed field
agree as soon as they agree on the pullbacks of rational functions along both projections. -/
theorem functionField_pullback_ringHom_ext {R : Type*} [CommRing R]
    {φ ψ : (pullback f g).functionField →+* R}
    (h₁ : ∀ a, φ (functionFieldMap (pullback.fst f g) a) =
      ψ (functionFieldMap (pullback.fst f g) a))
    (h₂ : ∀ b, φ (functionFieldMap (pullback.snd f g) b) =
      ψ (functionFieldMap (pullback.snd f g) b)) : φ = ψ := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  let := (functionFieldTensorToPullback k f g).toAlgebra
  have := isFractionRing_functionFieldTensorToPullback k f g
  refine IsLocalization.ringHom_ext (nonZeroDivisors (X.functionField ⊗[k] Y.functionField))
    (RingHom.ext fun t => t.inductionOn (fun a b => ?_)
      (fun x y hx hy => by simp only [map_add, hx, hy]))
  change φ (functionFieldTensorToPullback k f g (a ⊗ₜ b)) =
    ψ (functionFieldTensorToPullback k f g (a ⊗ₜ b))
  rw [functionFieldTensorToPullback_tmul, map_mul, map_mul, h₁, h₂]

/-- `AlgebraicGeometry.pullbackFunctionFieldEquiv` on `pr₁^* a`. -/
theorem pullbackFunctionFieldEquiv_fst (a : X.functionField) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    pullbackFunctionFieldEquiv k f g (functionFieldMap (pullback.fst f g) a) =
      algebraMap (X.functionField ⊗[k] Y.functionField) (FractionRing _) (a ⊗ₜ 1) := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  rw [← pullbackFunctionFieldEquiv_mul, map_one, mul_one]

/-- `AlgebraicGeometry.pullbackFunctionFieldEquiv` on `pr₂^* b`. -/
theorem pullbackFunctionFieldEquiv_snd (b : Y.functionField) :
    letI := stalkAlgebraOver k f (genericPoint X)
    letI := stalkAlgebraOver k g (genericPoint Y)
    pullbackFunctionFieldEquiv k f g (functionFieldMap (pullback.snd f g) b) =
      algebraMap (X.functionField ⊗[k] Y.functionField) (FractionRing _) (1 ⊗ₜ b) := by
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  rw [← pullbackFunctionFieldEquiv_mul, map_one, one_mul]

end PullbackExt

/-- `TensorProduct.fractionRingMap K₀ a` on the image of a pure tensor. -/
theorem _root_.TensorProduct.fractionRingMap_algebraMap_tmul {k K L K₀ : Type*} [Field k]
    [Field K] [Algebra k K] [Field L] [Algebra k L] [Field K₀] [Algebra k K₀]
    [IsDomain (K ⊗[k] K₀)] [IsDomain (L ⊗[k] K₀)] (a : K →ₐ[k] L) (x : K) (y : K₀) :
    TensorProduct.fractionRingMap K₀ a (algebraMap (K ⊗[k] K₀) _ (x ⊗ₜ y)) =
      algebraMap (L ⊗[k] K₀) _ (a x ⊗ₜ y) := by
  rw [TensorProduct.fractionRingMap_algebraMap, LinearMap.rTensor_tmul]
  rfl

namespace GenericQuotientFlat

open TensorProduct.RationalGroup

variable {k : Type u} [Field k]

/-- The `k`-algebra structure on the function field of an integral scheme over `Spec k`, through
its structure morphism. -/
abbrev functionFieldAlgebra (X : Over (Spec (.of k))) [IsIntegral X.left] :
    Algebra k X.left.functionField :=
  stalkAlgebraOver k X.hom (genericPoint X.left)

/-- The `k`-algebra structure on the function field of a fibre product of integral schemes over
`Spec k`, through the first projection. -/
abbrev pullbackFunctionFieldAlgebra {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (g : Y ⟶ Spec (.of k)) [IsIntegral (pullback f g)] :
    Algebra k (pullback f g).functionField :=
  stalkAlgebraOver k (pullback.fst f g ≫ f) (genericPoint (pullback f g : Scheme.{u}))

attribute [local instance] functionFieldAlgebra pullbackFunctionFieldAlgebra

/-- Over an algebraically closed field the tensor product of two domains is a domain: a domain
`B` over `k` is geometrically integral since `B ⊗[k] k̄ ≅ B`
(`Algebra.isGeometricallyIntegral_tfae`), so
`Algebra.IsGeometricallyIntegral.isDomain_tensorProduct` applies. -/
scoped instance isDomain_tensorProduct_of_isAlgClosed (A B : Type u) [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [CommRing B] [IsDomain B] [Algebra k B] :
    IsDomain (A ⊗[k] B) := by
  have he : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] AlgebraicClosure k :=
    AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k)) he
  have : Algebra.IsGeometricallyIntegral k B :=
    ((Algebra.isGeometricallyIntegral_tfae k B).out 4 1).mp <|
      Function.Injective.isDomain ((Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans
        (Algebra.TensorProduct.rid k k B)).toRingHom (AlgEquiv.injective _)
  exact Algebra.IsGeometricallyIntegral.isDomain_tensorProduct k A B

/-- Ring maps `Φ ∘ m^*` and `Ψ ∘ (K(G × G) ≅ Frac(K ⊗[k] K))`, for a dominant `m : P → G × G`,
agree once they agree on `pr₁^* a` and `pr₂^* b`. -/
private theorem apply_functionFieldMap_eq [IsAlgClosed k]
    (G : Over (Spec (.of k))) [IsIntegral G.left]
    {R : Type*} [CommRing R] {P : Scheme.{u}} [IsIntegral P]
    (m : P ⟶ pullback G.hom G.hom) [IsDominant m] (Φ : P.functionField →+* R)
    (Ψ : Sq k G.left.functionField →+* R)
    (h₁ : ∀ a, Φ (functionFieldMap m (functionFieldMap (pullback.fst G.hom G.hom) a)) =
      Ψ (pullbackFunctionFieldEquiv k G.hom G.hom
        (functionFieldMap (pullback.fst G.hom G.hom) a)))
    (h₂ : ∀ b, Φ (functionFieldMap m (functionFieldMap (pullback.snd G.hom G.hom) b)) =
      Ψ (pullbackFunctionFieldEquiv k G.hom G.hom
        (functionFieldMap (pullback.snd G.hom G.hom) b)))
    (z : (pullback G.hom G.hom).functionField) :
    Φ (functionFieldMap m z) = Ψ (pullbackFunctionFieldEquiv k G.hom G.hom z) :=
  DFunLike.congr_fun (functionField_pullback_ringHom_ext G.hom G.hom
    (φ := Φ.comp (functionFieldMap m))
    (ψ := Ψ.comp (pullbackFunctionFieldEquiv k G.hom G.hom).toRingHom) h₁ h₂) z

section Comul

variable [IsAlgClosed k] (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left]

/-- The action `(x, g) ↦ g x` of `G` on itself by left translation, with the acting factor
second. -/
abbrev actO : G ⊗ G ⟶ G := lift (snd G G) (fst G G) ≫ μ

/-- `((x, g), h) ↦ (g x, h)`. -/
abbrev actFirstO : (G ⊗ G) ⊗ G ⟶ G ⊗ G := actO G ▷ G

/-- `((x, g), h) ↦ (g, h)`. -/
abbrev lastTwoO : (G ⊗ G) ⊗ G ⟶ G ⊗ G := lift (fst _ _ ≫ snd G G) (snd _ _)

/-- `((x, g), h) ↦ (x, h g)`. -/
abbrev actLastTwoO : (G ⊗ G) ⊗ G ⟶ G ⊗ G := lift (fst _ _ ≫ fst G G) (lastTwoO G ≫ actO G)

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- Associativity of the action: `h (g x)` computed via `((x, g), h) ↦ (g x, h)` agrees with
`(h g) x` computed via `((x, g), h) ↦ (x, h g)`. -/
lemma actFirstO_actO : actFirstO G ≫ actO G = actLastTwoO G ≫ actO G := by
  simp only [actO, actFirstO, actLastTwoO, lastTwoO, comp_lift_assoc,
    CartesianMonoidalCategory.whiskerRight_snd, CartesianMonoidalCategory.whiskerRight_fst,
    lift_fst, lift_snd]
  exact (MonObj.lift_lift_assoc (snd (G ⊗ G) G) (fst (G ⊗ G) G ≫ snd G G)
    (fst (G ⊗ G) G ≫ fst G G)).symm

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- `x ↦ (x, 1)` is a section of the action `(x, g) ↦ g x`. -/
lemma actO_section : lift (𝟙 G) (toUnit G ≫ η) ≫ actO G = 𝟙 G := by
  rw [actO, ← Category.assoc, comp_lift, lift_snd, lift_fst, MonObj.lift_comp_one_left]

/-- The action `(x, g) ↦ g x` is dominant. -/
instance isDominant_actO : IsDominant (actO G).left :=
  isDominant_of_comp_eq_id _ (lift (𝟙 G) (toUnit G ≫ η)).left (by
    rw [← Over.comp_left, actO_section, Over.id_left])

/-- The morphism `((x, g), h) ↦ (g x, h)` is dominant. -/
instance isDominant_actFirstO : IsDominant (actFirstO G).left :=
  isDominant_of_comp_eq_id _ ((lift (𝟙 G) (toUnit G ≫ η)) ▷ G).left (by
    rw [← Over.comp_left, actFirstO, ← comp_whiskerRight, actO_section, id_whiskerRight,
      Over.id_left])

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- `(g, h) ↦ ((1, g), h)` is a section of `((x, g), h) ↦ (g, h)`. -/
lemma lastTwoO_section : lift (lift (toUnit _ ≫ η) (fst G G)) (snd G G) ≫ lastTwoO G = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [lastTwoO]

/-- The projection `((x, g), h) ↦ (g, h)` is dominant. -/
instance isDominant_lastTwoO : IsDominant (lastTwoO G).left :=
  isDominant_of_comp_eq_id _ (lift (lift (toUnit _ ≫ η) (fst G G)) (snd G G)).left (by
    rw [← Over.comp_left, lastTwoO_section, Over.id_left])

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- `(x, h) ↦ ((x, 1), h)` is a section of `((x, g), h) ↦ (x, h g)`. -/
lemma actLastTwoO_section :
    lift (lift (fst G G) (toUnit _ ≫ η)) (snd G G) ≫ actLastTwoO G = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [actLastTwoO, lastTwoO, actO, comp_lift_assoc]

/-- The morphism `((x, g), h) ↦ (x, h g)` is dominant. -/
instance isDominant_actLastTwoO : IsDominant (actLastTwoO G).left :=
  isDominant_of_comp_eq_id _ (lift (lift (fst G G) (toUnit _ ≫ η)) (snd G G)).left (by
    rw [← Over.comp_left, actLastTwoO_section, Over.id_left])

/-- `(x, g) ↦ g x` on `G ×_k G`. -/
def act : pullback G.hom G.hom ⟶ G.left := (actO G).left

/-- `((x, g), h) ↦ (g x, h)` on `(G ×_k G) ×_k G`. -/
def actFirst : pullback (pullback.fst G.hom G.hom ≫ G.hom) G.hom ⟶ pullback G.hom G.hom :=
  (actFirstO G).left

/-- `((x, g), h) ↦ (g, h)` on `(G ×_k G) ×_k G`. -/
def lastTwoMap : pullback (pullback.fst G.hom G.hom ≫ G.hom) G.hom ⟶ pullback G.hom G.hom :=
  (lastTwoO G).left

/-- `((x, g), h) ↦ (x, h g)` on `(G ×_k G) ×_k G`. -/
def actLastTwo : pullback (pullback.fst G.hom G.hom ≫ G.hom) G.hom ⟶ pullback G.hom G.hom :=
  (actLastTwoO G).left

/-- `AlgebraicGeometry.GenericQuotientFlat.act` is dominant. -/
instance : IsDominant (act G) := isDominant_actO G

/-- `AlgebraicGeometry.GenericQuotientFlat.actFirst` is dominant. -/
instance : IsDominant (actFirst G) := isDominant_actFirstO G

/-- `AlgebraicGeometry.GenericQuotientFlat.lastTwoMap` is dominant. -/
instance : IsDominant (lastTwoMap G) := isDominant_lastTwoO G

/-- `AlgebraicGeometry.GenericQuotientFlat.actLastTwo` is dominant. -/
instance : IsDominant (actLastTwo G) := isDominant_actLastTwoO G

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- The action `(x, g) ↦ g x` is a morphism over `Spec k`. -/
lemma act_comp : act G ≫ G.hom = pullback.fst G.hom G.hom ≫ G.hom := Over.w (actO G)

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- Associativity on `(G ×_k G) ×_k G`: `h (g x) = (h g) x`. -/
lemma actFirst_act : actFirst G ≫ act G = actLastTwo G ≫ act G :=
  congrArg (fun f => f.left) (actFirstO_actO G)

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- The first coordinate of `((x, g), h) ↦ (g x, h)` is `g x`. -/
lemma actFirst_fst : actFirst G ≫ pullback.fst G.hom G.hom =
    pullback.fst (pullback.fst G.hom G.hom ≫ G.hom) G.hom ≫ act G :=
  congrArg (fun f => f.left) (CartesianMonoidalCategory.whiskerRight_fst (actO G) G)

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- The second coordinate of `((x, g), h) ↦ (g x, h)` is `h`. -/
lemma actFirst_snd : actFirst G ≫ pullback.snd G.hom G.hom =
    pullback.snd (pullback.fst G.hom G.hom ≫ G.hom) G.hom :=
  congrArg (fun f => f.left) (CartesianMonoidalCategory.whiskerRight_snd (actO G) G)

omit [IsAlgClosed k] [GrpObj G] [IsIntegral G.left] in
/-- The first coordinate of `((x, g), h) ↦ (g, h)` is `g`. -/
lemma lastTwoMap_fst : lastTwoMap G ≫ pullback.fst G.hom G.hom =
    pullback.fst (pullback.fst G.hom G.hom ≫ G.hom) G.hom ≫ pullback.snd G.hom G.hom :=
  congrArg (fun f => f.left) (lift_fst (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G))

omit [IsAlgClosed k] [GrpObj G] [IsIntegral G.left] in
/-- The second coordinate of `((x, g), h) ↦ (g, h)` is `h`. -/
lemma lastTwoMap_snd : lastTwoMap G ≫ pullback.snd G.hom G.hom =
    pullback.snd (pullback.fst G.hom G.hom ≫ G.hom) G.hom :=
  congrArg (fun f => f.left) (lift_snd (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G))

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- The first coordinate of `((x, g), h) ↦ (x, h g)` is `x`. -/
lemma actLastTwo_fst : actLastTwo G ≫ pullback.fst G.hom G.hom =
    pullback.fst (pullback.fst G.hom G.hom ≫ G.hom) G.hom ≫ pullback.fst G.hom G.hom :=
  congrArg (fun f => f.left) (lift_fst (fst (G ⊗ G) G ≫ fst G G) (lastTwoO G ≫ actO G))

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- The second coordinate of `((x, g), h) ↦ (x, h g)` is `h g`, the action applied to `(g, h)`. -/
lemma actLastTwo_snd : actLastTwo G ≫ pullback.snd G.hom G.hom = lastTwoMap G ≫ act G :=
  congrArg (fun f => f.left) (lift_snd (fst (G ⊗ G) G ≫ fst G G) (lastTwoO G ≫ actO G))

/-- **The rational group of `G`**: the comultiplication `Δ : K → Frac(K ⊗[k] K)`,
`Δ b (x, g) = b (g x)`, induced by the dominant morphism `(x, g) ↦ g x` and the identification
`K(G × G) ≅ Frac(K ⊗[k] K)` (`AlgebraicGeometry.pullbackFunctionFieldAlgEquiv`). -/
def functionFieldComul : G.left.functionField →ₐ[k] Sq k G.left.functionField :=
  (pullbackFunctionFieldAlgEquiv k G.hom G.hom).toAlgHom.comp
    (functionFieldMapAlgHom k G.hom (act G) (pullback.fst G.hom G.hom ≫ G.hom) (act_comp G))

/-- `Δ b` is the image of the pullback of `b` along `(x, g) ↦ g x` under
`K(G × G) ≅ Frac(K ⊗[k] K)`. -/
lemma functionFieldComul_apply (b : G.left.functionField) :
    functionFieldComul G b =
      pullbackFunctionFieldEquiv k G.hom G.hom (functionFieldMap (act G) b) :=
  rfl

/-- The map `K((G × G) × G) → Frac(Frac(K ⊗[k] K) ⊗[k] K)`, the identification of the function
field of a product applied twice. -/
def cubeMap : (pullback (pullback.fst G.hom G.hom ≫ G.hom) G.hom).functionField →+*
    Cube k G.left.functionField :=
  (TensorProduct.fractionRingMap G.left.functionField
      (pullbackFunctionFieldAlgEquiv k G.hom G.hom).toAlgHom).comp
    (pullbackFunctionFieldEquiv k (pullback.fst G.hom G.hom ≫ G.hom) G.hom).toRingHom

omit [GrpObj G] in
/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` sends the pullback of `z ∈ K(G × G)` along
the first projection to `z ⊗ 1`. -/
lemma cubeMap_fst (z : (pullback G.hom G.hom).functionField) :
    cubeMap G (functionFieldMap (pullback.fst (pullback.fst G.hom G.hom ≫ G.hom) G.hom) z) =
      algebraMap (Sq k G.left.functionField ⊗[k] G.left.functionField) _
        (pullbackFunctionFieldEquiv k G.hom G.hom z ⊗ₜ 1) := by
  rw [cubeMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    pullbackFunctionFieldEquiv_fst, TensorProduct.fractionRingMap_algebraMap,
    LinearMap.rTensor_tmul]
  rfl

omit [GrpObj G] in
/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` sends the pullback of `b ∈ K(G)` along the
second projection to `1 ⊗ b`. -/
lemma cubeMap_snd (b : G.left.functionField) :
    cubeMap G (functionFieldMap (pullback.snd (pullback.fst G.hom G.hom ≫ G.hom) G.hom) b) =
      algebraMap (Sq k G.left.functionField ⊗[k] G.left.functionField) _ (1 ⊗ₜ b) := by
  rw [cubeMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    pullbackFunctionFieldEquiv_snd, TensorProduct.fractionRingMap_algebraMap,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` on the pullback of `pr₁^* a` along
`((x, g), h) ↦ (g x, h)` is `(Δ ⊗ 1)~` applied to `pr₁^* a`. -/
lemma cubeMap_actFirst_fst (a : G.left.functionField) :
    cubeMap G (functionFieldMap (actFirst G) (functionFieldMap (pullback.fst G.hom G.hom) a)) =
      TensorProduct.fractionRingMap G.left.functionField (functionFieldComul G)
        (pullbackFunctionFieldEquiv k G.hom G.hom
          (functionFieldMap (pullback.fst G.hom G.hom) a)) := by
  rw [functionFieldMap_comp_apply _ _ (actFirst_fst G),
    ← functionFieldMap_comp_apply _ _ rfl, cubeMap_fst, ← functionFieldComul_apply,
    pullbackFunctionFieldEquiv_fst, TensorProduct.fractionRingMap_algebraMap_tmul]

/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` on the pullback of `pr₂^* b` along
`((x, g), h) ↦ (g x, h)` is `(Δ ⊗ 1)~` applied to `pr₂^* b`. -/
lemma cubeMap_actFirst_snd (b : G.left.functionField) :
    cubeMap G (functionFieldMap (actFirst G) (functionFieldMap (pullback.snd G.hom G.hom) b)) =
      TensorProduct.fractionRingMap G.left.functionField (functionFieldComul G)
        (pullbackFunctionFieldEquiv k G.hom G.hom
          (functionFieldMap (pullback.snd G.hom G.hom) b)) := by
  rw [functionFieldMap_comp_apply _ _ (actFirst_snd G), cubeMap_snd,
    pullbackFunctionFieldEquiv_snd, TensorProduct.fractionRingMap_algebraMap_tmul,
    map_one (functionFieldComul G)]

/-- The pullback along `((x, g), h) ↦ (g x, h)` is `(Δ ⊗ 1)~`. -/
lemma cubeMap_actFirst (z : (pullback G.hom G.hom).functionField) :
    cubeMap G (functionFieldMap (actFirst G) z) =
      TensorProduct.fractionRingMap G.left.functionField (functionFieldComul G)
        (pullbackFunctionFieldEquiv k G.hom G.hom z) :=
  apply_functionFieldMap_eq G _ (cubeMap G)
    (TensorProduct.fractionRingMap G.left.functionField (functionFieldComul G))
    (cubeMap_actFirst_fst G) (cubeMap_actFirst_snd G) z

/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` on the pullback of `pr₁^* a` along
`((x, g), h) ↦ (g, h)` is the embedding of `pr₁^* a` into the last two slots. -/
lemma cubeMap_lastTwoMap_fst (a : G.left.functionField) :
    cubeMap G (functionFieldMap (lastTwoMap G) (functionFieldMap (pullback.fst G.hom G.hom) a)) =
      lastTwo k G.left.functionField
        (pullbackFunctionFieldEquiv k G.hom G.hom
          (functionFieldMap (pullback.fst G.hom G.hom) a)) := by
  rw [functionFieldMap_comp_apply _ _ (lastTwoMap_fst G),
    ← functionFieldMap_comp_apply _ _ rfl, cubeMap_fst, pullbackFunctionFieldEquiv_snd,
    pullbackFunctionFieldEquiv_fst, lastTwo_algebraMap (k := k) (K := G.left.functionField),
    lastTwoHom_tmul (k := k) (K := G.left.functionField)]
  rfl

/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` on the pullback of `pr₂^* b` along
`((x, g), h) ↦ (g, h)` is the embedding of `pr₂^* b` into the last two slots. -/
lemma cubeMap_lastTwoMap_snd (b : G.left.functionField) :
    cubeMap G (functionFieldMap (lastTwoMap G) (functionFieldMap (pullback.snd G.hom G.hom) b)) =
      lastTwo k G.left.functionField
        (pullbackFunctionFieldEquiv k G.hom G.hom
          (functionFieldMap (pullback.snd G.hom G.hom) b)) := by
  rw [functionFieldMap_comp_apply _ _ (lastTwoMap_snd G), cubeMap_snd,
    pullbackFunctionFieldEquiv_snd, lastTwo_algebraMap (k := k) (K := G.left.functionField),
    lastTwoHom_tmul (k := k) (K := G.left.functionField),
    ← Algebra.TensorProduct.one_def, map_one (toSq k G.left.functionField)]

/-- The pullback along `((x, g), h) ↦ (g, h)` is the embedding of the last two slots. -/
lemma cubeMap_lastTwoMap (z : (pullback G.hom G.hom).functionField) :
    cubeMap G (functionFieldMap (lastTwoMap G) z) =
      lastTwo k G.left.functionField (pullbackFunctionFieldEquiv k G.hom G.hom z) :=
  apply_functionFieldMap_eq G _ (cubeMap G) (lastTwo k G.left.functionField).toRingHom
    (cubeMap_lastTwoMap_fst G) (cubeMap_lastTwoMap_snd G) z

/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` on the pullback of `pr₁^* a` along
`((x, g), h) ↦ (x, h g)` is `(1 ⊗ Δ)~` applied to `pr₁^* a`. -/
lemma cubeMap_actLastTwo_fst (a : G.left.functionField) :
    cubeMap G (functionFieldMap (actLastTwo G) (functionFieldMap (pullback.fst G.hom G.hom) a)) =
      comulLastTwo (functionFieldComul G)
        (pullbackFunctionFieldEquiv k G.hom G.hom
          (functionFieldMap (pullback.fst G.hom G.hom) a)) := by
  rw [functionFieldMap_comp_apply _ _ (actLastTwo_fst G),
    ← functionFieldMap_comp_apply _ _ rfl, cubeMap_fst, pullbackFunctionFieldEquiv_fst,
    comulLastTwo_algebraMap_tmul (k := k) (K := G.left.functionField),
    map_one (functionFieldComul G), map_one (lastTwo k G.left.functionField), mul_one,
    firstHom_apply (k := k) (K := G.left.functionField)]
  rfl

/-- `AlgebraicGeometry.GenericQuotientFlat.cubeMap` on the pullback of `pr₂^* b` along
`((x, g), h) ↦ (x, h g)` is `(1 ⊗ Δ)~` applied to `pr₂^* b`. -/
lemma cubeMap_actLastTwo_snd (b : G.left.functionField) :
    cubeMap G (functionFieldMap (actLastTwo G) (functionFieldMap (pullback.snd G.hom G.hom) b)) =
      comulLastTwo (functionFieldComul G)
        (pullbackFunctionFieldEquiv k G.hom G.hom
          (functionFieldMap (pullback.snd G.hom G.hom) b)) := by
  rw [functionFieldMap_comp_apply _ _ (actLastTwo_snd G),
    ← functionFieldMap_comp_apply _ _ rfl, cubeMap_lastTwoMap, ← functionFieldComul_apply,
    pullbackFunctionFieldEquiv_snd,
    comulLastTwo_algebraMap_tmul (k := k) (K := G.left.functionField),
    map_one (firstHom k G.left.functionField), one_mul]

/-- The pullback along `((x, g), h) ↦ (x, h g)` is `(1 ⊗ Δ)~`. -/
lemma cubeMap_actLastTwo (z : (pullback G.hom G.hom).functionField) :
    cubeMap G (functionFieldMap (actLastTwo G) z) =
      comulLastTwo (functionFieldComul G) (pullbackFunctionFieldEquiv k G.hom G.hom z) :=
  apply_functionFieldMap_eq G _ (cubeMap G) (comulLastTwo (functionFieldComul G)).toRingHom
    (cubeMap_actLastTwo_fst G) (cubeMap_actLastTwo_snd G) z

/-- **Coassociativity of the rational group of `G`**: `(Δ ⊗ 1)~ ∘ Δ = (1 ⊗ Δ)~ ∘ Δ`, both sides
being the pullback of rational functions along `((x, g), h) ↦ h g x`. -/
theorem functionFieldComul_coassoc (x : G.left.functionField) :
    TensorProduct.fractionRingMap G.left.functionField (functionFieldComul G)
        (functionFieldComul G x) =
      comulLastTwo (functionFieldComul G) (functionFieldComul G x) := by
  rw [functionFieldComul_apply, ← cubeMap_actFirst, ← cubeMap_actLastTwo,
    functionFieldMap_comp_apply _ _ (actFirst_act G), functionFieldMap_comp_apply _ _ rfl]

/-- **Left-invariant subfields of the function field of `G`** (Perrin, thèse, III 2.2.1): every
finite set of rational functions on an integral group scheme `G` over an algebraically closed
field lies in a finitely generated intermediate field `K₁` of `K(G) / k` with
`Δ(K₁) ⊆ Frac(K₁ ⊗[k] K(G))`, i.e. `b (g x)` is a rational function of `(x, g)` defined over
`K₁` in the first variable for every `b ∈ K₁`. -/
theorem exists_fg_leftInvariant_functionField (s : Finset G.left.functionField) :
    ∃ K₁ : IntermediateField k G.left.functionField, K₁.FG ∧
      (s : Set G.left.functionField) ⊆ (K₁ : Set G.left.functionField) ∧
      ∀ y ∈ K₁, functionFieldComul G y ∈
        Set.range (TensorProduct.fractionRingMap G.left.functionField K₁.val) :=
  exists_fg_leftInvariant_intermediateField (functionFieldComul G) (functionFieldComul_coassoc G) s

end Comul

section Swap

variable [IsAlgClosed k] (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left]

/-- `(a, b) ↦ (b, a)` on `G ×_k G`. -/
def swapMap : pullback G.hom G.hom ⟶ pullback G.hom G.hom := (lift (snd G G) (fst G G)).left

omit [IsAlgClosed k] [GrpObj G] [IsIntegral G.left] in
/-- The swap `(a, b) ↦ (b, a)` of `G ×_k G` is an involution. -/
lemma swapMap_swapMap : swapMap G ≫ swapMap G = 𝟙 _ := by
  have : lift (snd G G) (fst G G) ≫ lift (snd G G) (fst G G) = 𝟙 (G ⊗ G) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [swapMap, ← Over.comp_left, this, Over.id_left]
  rfl

/-- The swap `(a, b) ↦ (b, a)` of `G ×_k G` is dominant. -/
instance isDominant_swapMap : IsDominant (swapMap G) :=
  isDominant_of_comp_eq_id _ (swapMap G) (swapMap_swapMap G)

omit [IsAlgClosed k] [GrpObj G] [IsIntegral G.left] in
/-- The first coordinate of the swap of `(a, b)` is `b`. -/
lemma swapMap_fst : swapMap G ≫ pullback.fst G.hom G.hom = pullback.snd G.hom G.hom :=
  congrArg (fun f => f.left) (lift_fst (snd G G) (fst G G))

omit [IsAlgClosed k] [GrpObj G] [IsIntegral G.left] in
/-- The second coordinate of the swap of `(a, b)` is `a`. -/
lemma swapMap_snd : swapMap G ≫ pullback.snd G.hom G.hom = pullback.fst G.hom G.hom :=
  congrArg (fun f => f.left) (lift_snd (snd G G) (fst G G))

omit [IsAlgClosed k] [IsIntegral G.left] in
/-- The action `(x, g) ↦ g x` precomposed with the swap is the multiplication `(a, b) ↦ a b`. -/
lemma swapMap_act : swapMap G ≫ act G = μ[G].left := by
  rw [swapMap, act, ← Over.comp_left, actO, ← Category.assoc, comp_lift, lift_snd, lift_fst,
    lift_fst_snd, Category.id_comp]

/-- The multiplication `μ : G ×_k G → G` is dominant. -/
instance isDominant_mu : IsDominant μ[G].left :=
  isDominant_of_comp_eq_id _ (lift (𝟙 G) (toUnit G ≫ η)).left (by
    rw [← Over.comp_left, MonObj.lift_comp_one_right, Over.id_left])

/-- The swap of the two factors of `Frac(K ⊗[k] K)`. -/
def sqSwap : Sq k G.left.functionField →+* Sq k G.left.functionField :=
  (IsFractionRing.ringEquivOfRingEquiv (K := Sq k G.left.functionField)
    (L := Sq k G.left.functionField) (Algebra.TensorProduct.comm k G.left.functionField
      G.left.functionField).toRingEquiv).toRingHom

omit [IsAlgClosed k] [GrpObj G] in
/-- `AlgebraicGeometry.GenericQuotientFlat.sqSwap` sends `a ⊗ b` to `b ⊗ a`. -/
lemma sqSwap_algebraMap_tmul (a b : G.left.functionField) :
    sqSwap G (algebraMap (G.left.functionField ⊗[k] G.left.functionField) _ (a ⊗ₜ b)) =
      algebraMap (G.left.functionField ⊗[k] G.left.functionField) _ (b ⊗ₜ a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

omit [GrpObj G] in
/-- The swap of `G ×_k G` acts on `pr₁^* a` by swapping the factors of `Frac(K ⊗[k] K)`. -/
lemma pullbackFunctionFieldEquiv_swapMap_fst (a : G.left.functionField) :
    pullbackFunctionFieldEquiv k G.hom G.hom
        (functionFieldMap (swapMap G) (functionFieldMap (pullback.fst G.hom G.hom) a)) =
      sqSwap G (pullbackFunctionFieldEquiv k G.hom G.hom
        (functionFieldMap (pullback.fst G.hom G.hom) a)) := by
  rw [functionFieldMap_comp_apply _ _ (swapMap_fst G), pullbackFunctionFieldEquiv_snd,
    pullbackFunctionFieldEquiv_fst, sqSwap_algebraMap_tmul]

omit [GrpObj G] in
/-- The swap of `G ×_k G` acts on `pr₂^* b` by swapping the factors of `Frac(K ⊗[k] K)`. -/
lemma pullbackFunctionFieldEquiv_swapMap_snd (b : G.left.functionField) :
    pullbackFunctionFieldEquiv k G.hom G.hom
        (functionFieldMap (swapMap G) (functionFieldMap (pullback.snd G.hom G.hom) b)) =
      sqSwap G (pullbackFunctionFieldEquiv k G.hom G.hom
        (functionFieldMap (pullback.snd G.hom G.hom) b)) := by
  rw [functionFieldMap_comp_apply _ _ (swapMap_snd G), pullbackFunctionFieldEquiv_fst,
    pullbackFunctionFieldEquiv_snd, sqSwap_algebraMap_tmul]

omit [GrpObj G] in
/-- The swap `(a, b) ↦ (b, a)` of `G ×_k G` acts on `Frac(K ⊗[k] K)` by swapping the factors. -/
lemma pullbackFunctionFieldEquiv_swapMap (z : (pullback G.hom G.hom).functionField) :
    pullbackFunctionFieldEquiv k G.hom G.hom (functionFieldMap (swapMap G) z) =
      sqSwap G (pullbackFunctionFieldEquiv k G.hom G.hom z) :=
  apply_functionFieldMap_eq G _ (pullbackFunctionFieldEquiv k G.hom G.hom).toRingHom (sqSwap G)
    (pullbackFunctionFieldEquiv_swapMap_fst G) (pullbackFunctionFieldEquiv_swapMap_snd G) z

/-- **The multiplication on function fields**: `μ^* b` is the swap of `Δ b`, i.e.
`b (a b') = (Δ b) (b', a)`. -/
theorem pullbackFunctionFieldEquiv_mu (b : G.left.functionField) :
    pullbackFunctionFieldEquiv k G.hom G.hom (functionFieldMap μ[G].left b) =
      sqSwap G (functionFieldComul G b) := by
  rw [← functionFieldMap_comp_apply _ _ (swapMap_act G), pullbackFunctionFieldEquiv_swapMap,
    functionFieldComul_apply]

omit [IsAlgClosed k] [GrpObj G] in
/-- `id ⊗ ρ : K ⊗[k] L → K ⊗[k] K` is injective for a `k`-algebra map `ρ` of fields. -/
lemma injective_tensorProductMap_id {L : Type u} [Field L] [Algebra k L]
    (ρ : L →ₐ[k] G.left.functionField) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k G.left.functionField) ρ) := by
  have h : ⇑(Algebra.TensorProduct.map (AlgHom.id k G.left.functionField) ρ) =
      ⇑(ρ.toLinearMap.lTensor G.left.functionField) := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ ρ.toRingHom.injective

/-- **Left invariance read on `μ`.**  If `Δ b` is defined over `ρ : L → K(G)` in the first slot
(e.g. `ρ = K₁.val` for the left-invariant subfields of `exists_fg_leftInvariant_functionField`),
then `μ^* b ∈ K(G × G) ≅ Frac(K ⊗[k] K)` is defined over `ρ` in the second slot. -/
theorem pullbackFunctionFieldEquiv_mu_mem_range {L : Type u} [Field L] [Algebra k L]
    (ρ : L →ₐ[k] G.left.functionField) (b : G.left.functionField)
    (hb : functionFieldComul G b ∈
      Set.range (TensorProduct.fractionRingMap G.left.functionField ρ)) :
    pullbackFunctionFieldEquiv k G.hom G.hom (functionFieldMap μ[G].left b) ∈
      Set.range (IsFractionRing.map (K := FractionRing (G.left.functionField ⊗[k] L))
        (L := Sq k G.left.functionField) (j := (Algebra.TensorProduct.map
          (AlgHom.id k G.left.functionField) ρ).toRingHom)
          (injective_tensorProductMap_id G ρ)) := by
  obtain ⟨w, hw⟩ := hb
  let swapL : FractionRing (L ⊗[k] G.left.functionField) →+*
      FractionRing (G.left.functionField ⊗[k] L) :=
    (IsFractionRing.ringEquivOfRingEquiv (Algebra.TensorProduct.comm k L
      G.left.functionField).toRingEquiv).toRingHom
  refine ⟨swapL w, ?_⟩
  rw [pullbackFunctionFieldEquiv_mu, ← hw]
  have H : (IsFractionRing.map (K := FractionRing (G.left.functionField ⊗[k] L))
        (L := Sq k G.left.functionField) (j := (Algebra.TensorProduct.map
          (AlgHom.id k G.left.functionField) ρ).toRingHom)
          (injective_tensorProductMap_id G ρ)).comp swapL =
      (sqSwap G).comp (TensorProduct.fractionRingMap G.left.functionField ρ) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (L ⊗[k] G.left.functionField))
      (RingHom.ext fun t => t.inductionOn (fun l c => ?_)
        (fun x y hx hy => by simp only [map_add, hx, hy]))
    simp only [RingHom.comp_apply]
    rw [TensorProduct.fractionRingMap_algebraMap_tmul, sqSwap_algebraMap_tmul]
    simp only [swapL, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rw [IsFractionRing.map, IsLocalization.map_eq]
    rfl
  exact DFunLike.congr_fun H w

/-- The first projection `G ×_k G → G` is dominant. -/
instance isDominant_fst_left : IsDominant (fst G G).left :=
  inferInstanceAs (IsDominant (pullback.fst G.hom G.hom))

/-- The second projection `G ×_k G → G` is dominant. -/
instance isDominant_snd_left : IsDominant (snd G G).left :=
  inferInstanceAs (IsDominant (pullback.snd G.hom G.hom))

/-- **Left invariance on `G × G`.**  Let `K₁ ⊆ K(G)` be left invariant (`Δ(K₁) ⊆ Frac(K₁ ⊗[k] K)`,
as produced by `exists_fg_leftInvariant_functionField`) and let `R` be a subfield of `K(G × G)`
containing `pr₁^* K(G)` and `pr₂^* K₁`.  Then `μ^* K₁ ⊆ R`: `b (a b')` is a rational function of
`a` and of `b'` through `K₁` only. -/
theorem functionFieldMap_mu_mem_of_leftInvariant
    (K₁ : IntermediateField k G.left.functionField)
    (hK₁ : ∀ y ∈ K₁, functionFieldComul G y ∈
      Set.range (TensorProduct.fractionRingMap G.left.functionField K₁.val))
    (R : Subfield (G ⊗ G).left.functionField)
    (h₁ : ∀ c, functionFieldMap (fst G G).left c ∈ R)
    (h₂ : ∀ b ∈ K₁, functionFieldMap (snd G G).left b ∈ R) :
    ∀ b ∈ K₁, functionFieldMap μ[G].left b ∈ R := by
  intro b hb
  obtain ⟨w, hw⟩ := pullbackFunctionFieldEquiv_mu_mem_range G K₁.val b (hK₁ b hb)
  let e := pullbackFunctionFieldEquiv k G.hom G.hom
  let ψ : FractionRing (G.left.functionField ⊗[k] K₁) →+* (G ⊗ G).left.functionField :=
    e.symm.toRingHom.comp (IsFractionRing.map (K := FractionRing (G.left.functionField ⊗[k] K₁))
      (L := Sq k G.left.functionField) (j := (Algebra.TensorProduct.map
        (AlgHom.id k G.left.functionField) K₁.val).toRingHom)
      (injective_tensorProductMap_id G K₁.val))
  have hμ : functionFieldMap μ[G].left b = ψ w := by
    change _ = e.symm _
    rw [hw, RingEquiv.symm_apply_apply]
  rw [hμ]
  refine TensorProduct.RationalGroup.map_mem_of_forall_algebraMap_mem
    (A := G.left.functionField ⊗[k] K₁) ψ R (fun t => ?_) w
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add]; exact R.add_mem hx hy
  | tmul c a =>
    have h : ψ (algebraMap (G.left.functionField ⊗[k] K₁) _ (c ⊗ₜ a)) =
        functionFieldMap (pullback.fst G.hom G.hom) c *
          functionFieldMap (pullback.snd G.hom G.hom) (a : G.left.functionField) := by
      change e.symm (IsFractionRing.map _ (algebraMap (G.left.functionField ⊗[k] K₁) _
        (c ⊗ₜ a))) = _
      rw [IsFractionRing.map, IsLocalization.map_eq, RingEquiv.symm_apply_eq]
      exact (pullbackFunctionFieldEquiv_mul k G.hom G.hom c (a : G.left.functionField)).symm
    rw [h]
    exact R.mul_mem (h₁ c) (h₂ a a.2)

end Swap

end GenericQuotientFlat

end AlgebraicGeometry

end
