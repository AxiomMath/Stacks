module

public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsScaling
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Module.Adequate.SplittingRepresentabilityDomain

/-!
# The dual-number scaling on module-valued functors on a domain of pairs

The dual-number scaling `T^*` and its structure maps on module-valued functors on a full
subcategory `Qr` of pairs closed under the dual-number pairs `(C[ε], V ⊕ εV)`, with module values
in any universe containing the pairs, and the vanishing of `Ext^i(L, M̲)` for `i > 0` and every
linearly adequate functor `L` on a domain of algebras with a base object.

## Main definitions

* `AdequateFunctor.dualScalingOn`: the exact endofunctor `T^*` on a domain of pairs.
* `AdequateFunctor.dualScalingInlOn`, `AdequateFunctor.dualScalingInrOn`: `p` and `a`.
* `AdequateFunctor.dualScalingEpsOn`: `τ`.
* `AdequateFunctor.symPairExtensionOn`: the functor `ψ_N^* M̲` on a domain of pairs.
* `AdequateFunctor.pairsWeightOneProjectionOn`: its weight-one projection `Π`.

## Main results

* `AdequateFunctor.dualScalingInrOn_app_tautological`: `a = p ≫ τ` on `V`.
* `AdequateFunctor.pairsWeightOneOutOn_comp_inOn`: `Π` factors through `ψ_A^* (N ⊗ M)̲`.
* `AdequateFunctor.projective_unitLinearPairPullbackOn`: `φ_A^* V` is projective on a domain of
  algebras with a base object.
* `AdequateFunctor.subsingleton_zExt_isLinearlyAdequate_moduleExtensionOn`: `Ext^i(L, M̲) = 0`
  for `i > 0`, for every linearly adequate functor `L` on a domain of algebras with a base object.

## References

* [Stacks Project, Tag 06ZH](https://stacks.math.columbia.edu/tag/06ZH)
-/

@[expose] public section

universe t t' w v u

open CategoryTheory Opposite TrivSqZeroExt
open scoped TensorProduct

namespace AdequateFunctor

section EndofunctorOn

variable {A : Type u} [CommRing A] {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}
  (hQ : ∀ X, Qr X → Qr (dualNumberPair X))

/-- The dual-number pair functor `(C, V) ↦ (C[ε], V ⊕ εV)` on a domain of pairs closed under
it. -/
noncomputable abbrev dualNumberPairFunctorOn : Qr.FullSubcategory ⥤ Qr.FullSubcategory :=
  Qr.lift (Qr.ι ⋙ dualNumberPairFunctor) fun X ↦ hQ X.obj X.property

/-- The inclusions `C → C[ε]` on a domain of pairs. -/
noncomputable def dualNumberRingHomOn :
    pairRingDiagramOn Qr ⟶ (dualNumberPairFunctorOn hQ).op.op ⋙ pairRingDiagramOn Qr :=
  Functor.whiskerLeft Qr.ι.op.op (dualNumberRingHom.{v} A)

/-- **The dual-number scaling** `T^*` on a domain of pairs: restriction along
`(C, V) ↦ (C[ε], V ⊕ εV)`. -/
noncomputable abbrev dualScalingOn :
    PresheafOfModules.{w} (pairRingDiagramOn Qr) ⥤ PresheafOfModules.{w} (pairRingDiagramOn Qr) :=
  PresheafOfModules.pushforward.{w} (dualNumberRingHomOn hQ)

open Stacks.AlgebraicGeometry.RestrictionExact CategoryTheory.Limits in
/-- The dual-number scaling `T^*` on a domain of pairs is additive. -/
instance dualScalingOn_additive : (dualScalingOn.{w} hQ).Additive :=
  additive_presheafPushforward _

open Stacks.AlgebraicGeometry.RestrictionExact CategoryTheory.Limits in
/-- The dual-number scaling `T^*` on a domain of pairs is left exact. -/
instance dualScalingOn_preservesFiniteLimits : PreservesFiniteLimits (dualScalingOn.{w} hQ) :=
  preservesFiniteLimits_presheafPushforward _

open CategoryTheory.Limits in
/-- The dual-number scaling `T^*` on a domain of pairs is right exact. -/
instance dualScalingOn_preservesFiniteColimits :
    PreservesFiniteColimits (dualScalingOn.{w} hQ) :=
  preservesFiniteColimits_presheafPushforward _

/-- The morphism `X ⟶ T X` of the domain of pairs given by a map of pairs `X → (C[ε], V ⊕ εV)`. -/
noncomputable abbrev dualNumberPairHomOn
    (κ : ∀ X : AlgebraModulePair.{max u v} A, X ⟶ dualNumberPair X)
    (X : Qr.FullSubcategory) : X ⟶ (dualNumberPairFunctorOn hQ).obj X :=
  ObjectProperty.homMk (κ X.obj)

/-- A natural transformation `𝟭 ⟶ T^*` on a domain of pairs from natural maps of pairs
`X → (C[ε], V ⊕ εV)` lying over `C → C[ε]`. -/
noncomputable def dualScalingNatTransOn
    (κ : ∀ X : AlgebraModulePair.{max u v} A, X ⟶ dualNumberPair X)
    (hbase : ∀ X, (κ X).base = inlAlgHom A X.algebra X.algebra)
    (hnat : ∀ {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y),
      g ≫ κ Y = κ X ≫ dualNumberPairMap g) :
    𝟭 (PresheafOfModules.{w} (pairRingDiagramOn Qr)) ⟶ dualScalingOn.{w} hQ where
  app Z :=
    { app X := ModuleCat.ofHom (X := Z.obj X) (Y := ((dualScalingOn.{w} hQ).obj Z).obj X)
        { toFun := fun z ↦ Z.map (dualNumberPairHomOn hQ κ X.unop.unop).op.op z
          map_add' := fun z z' ↦ map_add (Z.map (dualNumberPairHomOn hQ κ X.unop.unop).op.op).hom
            z z'
          map_smul' := fun c z ↦ by
            refine (PresheafOfModules.map_smul Z (dualNumberPairHomOn hQ κ X.unop.unop).op.op c
              z).trans ?_
            have hc : ((pairRingDiagramOn Qr).map
                (dualNumberPairHomOn hQ κ X.unop.unop).op.op).hom c =
                ((dualNumberRingHomOn hQ).app X).hom c :=
              DFunLike.congr_fun (hbase X.unop.unop.obj) c
            rw [hc]
            rfl }
      naturality {X Y} g := by
        ext z
        change Z.map (dualNumberPairHomOn hQ κ Y.unop.unop).op.op (Z.map g z) =
          Z.map ((dualNumberPairFunctorOn hQ).map g.unop.unop).op.op
            (Z.map (dualNumberPairHomOn hQ κ X.unop.unop).op.op z)
        rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
        refine Z.congr_map_apply ?_ z
        have h : g.unop.unop ≫ dualNumberPairHomOn hQ κ Y.unop.unop =
            dualNumberPairHomOn hQ κ X.unop.unop ≫ (dualNumberPairFunctorOn hQ).map g.unop.unop :=
          ObjectProperty.hom_ext _ (hnat g.unop.unop.hom)
        exact congrArg (fun f ↦ f.op.op) h }
  naturality Z Z' α := by
    refine PresheafOfModules.hom_ext fun X ↦ ?_
    ext z
    exact (PresheafOfModules.naturality_apply α (dualNumberPairHomOn hQ κ X.unop.unop).op.op
      z).symm

/-- `p : 𝟭 ⟶ T^*` on a domain of pairs, from `v ↦ (v, 0)`. -/
noncomputable abbrev dualScalingInlOn :
    𝟭 (PresheafOfModules.{w} (pairRingDiagramOn Qr)) ⟶ dualScalingOn.{w} hQ :=
  dualScalingNatTransOn hQ dualNumberPairInl (fun _ ↦ rfl) dualNumberPairInl_naturality

/-- `a : 𝟭 ⟶ T^*` on a domain of pairs, from `v ↦ (0, v) = ε v`. -/
noncomputable abbrev dualScalingInrOn :
    𝟭 (PresheafOfModules.{w} (pairRingDiagramOn Qr)) ⟶ dualScalingOn.{w} hQ :=
  dualScalingNatTransOn hQ dualNumberPairInr (fun _ ↦ rfl) dualNumberPairInr_naturality

/-- The element `ε` of `C[ε]`, as a scalar of the ring diagram of a domain of pairs at the
dual-number pair. -/
noncomputable abbrev dualEpsOn (X : Qr.FullSubcategory) :
    (pairRingDiagramOn Qr).obj (op (op ((dualNumberPairFunctorOn hQ).obj X))) :=
  dualEps X.obj

/-- Multiplication by `ε` on the value of a module-valued functor on a domain of pairs at a
dual-number pair. -/
noncomputable def dualEpsSmulOn (Z : PresheafOfModules.{w} (pairRingDiagramOn Qr))
    (X : Qr.FullSubcategory) :
    Z.obj (op (op ((dualNumberPairFunctorOn hQ).obj X))) →ₗ[
      (pairRingDiagramOn Qr).obj (op (op ((dualNumberPairFunctorOn hQ).obj X)))]
      Z.obj (op (op ((dualNumberPairFunctorOn hQ).obj X))) :=
  { toFun := fun z ↦ dualEpsOn hQ X • z
    map_add' := fun z z' ↦ smul_add _ z z'
    map_smul' := fun c z ↦ by
      have hc : dualEpsOn hQ X * c = c * dualEpsOn hQ X :=
        mul_comm (G := (dualNumberPair X.obj).algebra) _ _
      change dualEpsOn hQ X • c • z = c • dualEpsOn hQ X • z
      rw [smul_smul, smul_smul, hc] }

/-- Multiplication by `ε` commutes with the restriction maps along the dual-number pair
functor. -/
lemma dualEpsSmulOn_map (Z : PresheafOfModules.{w} (pairRingDiagramOn Qr))
    {X Y : Qr.FullSubcategory} (g : X ⟶ Y)
    (z : Z.obj (op (op ((dualNumberPairFunctorOn hQ).obj X)))) :
    (Z.map ((dualNumberPairFunctorOn hQ).map g).op.op (dualEpsSmulOn hQ Z X z) :
        Z.obj (op (op ((dualNumberPairFunctorOn hQ).obj Y)))) =
      dualEpsSmulOn hQ Z Y (Z.map ((dualNumberPairFunctorOn hQ).map g).op.op z) := by
  have h : ((pairRingDiagramOn Qr).map ((dualNumberPairFunctorOn hQ).map g).op.op).hom
      (dualEpsOn hQ X) = dualEpsOn hQ Y :=
    TrivSqZeroExt.ext (map_zero g.hom.base) (map_one g.hom.base)
  exact (PresheafOfModules.map_smul Z ((dualNumberPairFunctorOn hQ).map g).op.op
    (dualEpsOn hQ X) z).trans
      (congrArg (fun r ↦ r • Z.map ((dualNumberPairFunctorOn hQ).map g).op.op z) h)

/-- `τ : T^* ⟶ T^*` on a domain of pairs, multiplication by `ε`. -/
noncomputable def dualScalingEpsOn : dualScalingOn.{w} hQ ⟶ dualScalingOn.{w} hQ where
  app Z :=
    { app X := ModuleCat.ofHom (X := ((dualScalingOn.{w} hQ).obj Z).obj X)
        (Y := ((dualScalingOn.{w} hQ).obj Z).obj X)
        { toFun := fun z ↦ dualEpsSmulOn hQ Z X.unop.unop z
          map_add' := fun z z' ↦ map_add (dualEpsSmulOn hQ Z X.unop.unop) z z'
          map_smul' := fun c z ↦ (dualEpsSmulOn hQ Z X.unop.unop).map_smul
            (((dualNumberRingHomOn hQ).app X).hom c) z }
      naturality {X Y} g := by
        ext z
        exact (dualEpsSmulOn_map hQ Z g.unop.unop z).symm }
  naturality {Z Z'} α := by
    refine PresheafOfModules.hom_ext fun X ↦ ?_
    ext z
    exact ((α.app (op (op ((dualNumberPairFunctorOn hQ).obj X.unop.unop)))).hom.map_smul
      (dualEpsOn hQ X.unop.unop) z).symm

variable (Qr) in
/-- The tautological module-valued functor `(C, V) ↦ V` on a domain of pairs, with values in
the universe `max u v w`. -/
noncomputable abbrev tautologicalPairModuleOn :
    PresheafOfModules.{max u v w} (pairRingDiagramOn Qr) :=
  (presheafOfModulesUliftFunctor.{w} (pairRingDiagramOn Qr)).obj
    ((PresheafOfModules.pushforward₀ Qr.ι.op (pairRingDiagram.{v} A)).obj
      (tautologicalPairModuleSmall.{v} A))

/-- **On the tautological functor, `a = p ≫ τ`**: `(0, v) = ε (v, 0)`. -/
lemma dualScalingInrOn_app_tautological :
    (dualScalingInrOn.{max u v w} hQ).app (tautologicalPairModuleOn.{w} Qr) =
      (dualScalingInlOn.{max u v w} hQ).app (tautologicalPairModuleOn.{w} Qr) ≫
        (dualScalingEpsOn.{max u v w} hQ).app (tautologicalPairModuleOn.{w} Qr) := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  ext z
  exact ULift.ext _ _ (dualNumberPairInr_eq_eps_smul X.unop.unop.obj z.down)

end EndofunctorOn

section ExtensionOn

variable {A : Type u} [CommRing A] {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}

attribute [local instance] symPairAlgebra

/-- **`ψ_N^* M̲` on a domain of pairs**: the module-valued functor
`(C, V) ↦ Sym_C(V ⊗_A N) ⊗_A M` on the allowed pairs, the restriction along `ψ_N` of the module
extension `B ↦ B ⊗_A M` on the allowed algebras. -/
noncomputable abbrev symPairExtensionOn {N : Type (max u v)} [AddCommGroup N] [Module A N]
    (h : PairsDomainClosed N Pr Qr) (M : ModuleCat.{max u v w} A) :
    PresheafOfModules.{max u v w} (pairRingDiagramOn Qr) :=
  (PresheafOfModules.pushforward.{max u v w} (symPairRingHomOn h)).obj
    ((moduleExtensionFunctorOn.{max u v w, v} Pr.ι).obj M)

variable {N N' : Type (max u v)} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
  (h : PairsDomainClosed N Pr Qr) (h' : PairsDomainClosed N' Pr Qr)

/-- A morphism `ψ_N^* M̲ ⟶ ψ_{N'}^* M'̲` on a domain of pairs from a family of `A`-linear maps on
the values which is linear over the algebra of each pair and natural in the pair. -/
noncomputable def symPairExtensionHomOn {M M' : ModuleCat.{max u v w} A}
    (L : ∀ X : AlgebraModulePair.{max u v} A,
      (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M →ₗ[A]
        (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) ⊗[A] M')
    (hL : ∀ (X : AlgebraModulePair.{max u v} A) (c : X.algebra) t,
      L X (algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c • t) =
        algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) c • L X t)
    (hnat : ∀ {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) t,
      L Y (TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id t) =
        TensorProduct.map (symPairMap N' g).toLinearMap LinearMap.id (L X t)) :
    symPairExtensionOn.{w} h M ⟶ symPairExtensionOn.{w} h' M' where
  app X := ModuleCat.ofHom (X := (symPairExtensionOn.{w} h M).obj X)
    (Y := (symPairExtensionOn.{w} h' M').obj X)
    { toFun := L X.unop.unop.obj
      map_add' := map_add _
      map_smul' := fun c t ↦ hL X.unop.unop.obj c t }
  naturality {X Y} g := by
    ext t
    exact hnat g.unop.unop.hom t

/-- The component of `AdequateFunctor.symPairExtensionHomOn` at a pair is the given linear map
on values. -/
@[simp] lemma symPairExtensionHomOn_app_apply {M M' : ModuleCat.{max u v w} A}
    (L : ∀ X : AlgebraModulePair.{max u v} A,
      (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M →ₗ[A]
        (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) ⊗[A] M') (hL) (hnat)
    (X : (Qr.FullSubcategory)ᵒᵖᵒᵖ) t :
    (symPairExtensionHomOn.{w} h h' L hL hnat).app X t = L X.unop.unop.obj t := rfl

/-- **The weight-one projection of `ψ_N^* M̲`** on a domain of pairs, `(ι ∘ λ) ⊗ M`. -/
noncomputable def pairsWeightOneProjectionOn (M : ModuleCat.{max u v w} A) :
    symPairExtensionOn.{w} h M ⟶ symPairExtensionOn.{w} h M :=
  symPairExtensionHomOn.{w} h h (fun X ↦ (symPairWeightOne N X).rTensor M)
    (fun X c t ↦ symPairWeightOne_rTensor_algebraMap_smul N X c t)
    (fun g t ↦ (symPairWeightOne_rTensor_naturality N (M' := M) g t :))

variable (hA : PairsDomainClosed (unitPairModule.{v} A) Pr Qr)

/-- **The comparison `ψ_N^* M̲ ⟶ ψ_A^* (N ⊗ M)̲`** on a domain of pairs. -/
noncomputable def pairsWeightOneOutOn (M : ModuleCat.{max u v w} A) :
    symPairExtensionOn.{w} h M ⟶ symPairExtensionOn.{w} hA (ModuleCat.of A (N ⊗[A] M)) :=
  symPairExtensionHomOn.{w} h hA (pairsWeightOneOutMap N M)
    (pairsWeightOneOutMap_algebraMap_smul N M)
    (fun g t ↦ (pairsWeightOneOutMap_naturality N M g t :))

/-- **The comparison `ψ_A^* (N ⊗ M)̲ ⟶ ψ_N^* M̲`** on a domain of pairs. -/
noncomputable def pairsWeightOneInOn (M : ModuleCat.{max u v w} A) :
    symPairExtensionOn.{w} hA (ModuleCat.of A (N ⊗[A] M)) ⟶ symPairExtensionOn.{w} h M :=
  symPairExtensionHomOn.{w} hA h (pairsWeightOneInMap N M)
    (pairsWeightOneInMap_algebraMap_smul N M)
    (fun g t ↦ (pairsWeightOneInMap_naturality N M g t :))

/-- **The weight-one projection factors through `ψ_A^* (N ⊗ M)̲`** on a domain of pairs. -/
theorem pairsWeightOneOutOn_comp_inOn (M : ModuleCat.{max u v w} A) :
    pairsWeightOneOutOn.{w} h hA M ≫ pairsWeightOneInOn.{w} h hA M =
      pairsWeightOneProjectionOn.{w} h M := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  ext t
  exact pairsWeightOneInMap_outMap N M X.unop.unop.obj t

end ExtensionOn

section UnitProjective

/-! ### `φ_A^* V` is projective

For the rank-one free module `A`, the restriction `φ_A^* V` of the tautological functor along
`φ_A : D ↦ (D, Hom_A(A, D))` is the functor `D ↦ Hom_A(A, D) ≅ D`. It is projective when the
domain of algebras has a base object. -/

variable {A : Type u} [CommRing A] {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}
  (hA : PairsDomainClosed (unitPairModule.{v} A) Pr Qr) (b : BaseAlgebraObject.{v} Pr.ι)

/-- `φ_A^* V : D ↦ Hom_A(A, D)` on a domain of algebras. -/
noncomputable abbrev unitLinearPairPullbackOn :
    PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι) :=
  (PresheafOfModules.pushforward.{max u v w} (linearPairRingHomOn hA)).obj
    (tautologicalPairModuleOn.{w} Qr)

/-- All morphisms out of the base object of a domain of algebras agree. -/
lemma BaseAlgebraObject.hom_eq {X : Pr.FullSubcategory} (f : b.base ⟶ X) : f = b.hom X := by
  refine Pr.ι.map_injective (CommAlgCat.hom_ext (AlgHom.ext fun t ↦ ?_))
  have key : ∀ g : b.base ⟶ X,
      (Pr.ι.map g).hom t = algebraMap A (Pr.ι.obj X : Type (max u v)) (b.equiv t).down := by
    intro g
    conv_lhs => rw [b.eq_algebraMap t]
    exact (Pr.ι.map g).hom.commutes _
  exact (key f).trans (key (b.hom X)).symm

/-- The value `a ↦ a · 1` of `φ_A^* V` at the base object. -/
noncomputable def unitElementOn : (unitLinearPairPullbackOn.{w} hA).obj b.obj :=
  (ULift.up ((Algebra.linearMap A (b.base.obj : Type (max u v))) ∘ₗ
    (ULift.moduleEquiv : unitPairModule.{v} A ≃ₗ[A] A).toLinearMap) :
    ULift.{w} (unitPairModule.{v} A →ₗ[A] (b.base.obj : Type (max u v))))

/-- An element of `φ_A^* V` at `D`, as a linear map `A → D`. -/
noncomputable abbrev unitLinearOn (X : (Pr.FullSubcategory)ᵒᵖᵒᵖ)
    (ℓ : (unitLinearPairPullbackOn.{w} hA).obj X) :
    unitPairModule.{v} A →ₗ[A] (X.unop.unop.obj : Type (max u v)) :=
  (show ULift.{w} (unitPairModule.{v} A →ₗ[A] (X.unop.unop.obj : Type (max u v))) from ℓ).down

/-- The scalar `ℓ(1)` of an element `ℓ` of `φ_A^* V`, as a scalar of the ring diagram. -/
noncomputable abbrev unitScalarOn (X : (Pr.FullSubcategory)ᵒᵖᵒᵖ)
    (ℓ : (unitLinearPairPullbackOn.{w} hA).obj X) : (algebraRingDiagramOn.{v} Pr.ι).obj X :=
  unitLinearOn hA X ℓ (ULift.up 1)

/-- The scalar of `r • ℓ` is `r` times the scalar of `ℓ`. -/
lemma unitScalarOn_smul (X : (Pr.FullSubcategory)ᵒᵖᵒᵖ) (r : (algebraRingDiagramOn.{v} Pr.ι).obj X)
    (ℓ : (unitLinearPairPullbackOn.{w} hA).obj X) :
    unitScalarOn hA X (r • ℓ) = r * unitScalarOn hA X ℓ := rfl

/-- The scalar of a sum is the sum of the scalars. -/
lemma unitScalarOn_add (X : (Pr.FullSubcategory)ᵒᵖᵒᵖ)
    (ℓ ℓ' : (unitLinearPairPullbackOn.{w} hA).obj X) :
    unitScalarOn hA X (ℓ + ℓ') = unitScalarOn hA X ℓ + unitScalarOn hA X ℓ' := rfl

/-- The scalar of a restricted element is the image of the scalar under the ring map. -/
lemma unitScalarOn_map {X Y : (Pr.FullSubcategory)ᵒᵖᵒᵖ} (φ : X ⟶ Y)
    (ℓ : (unitLinearPairPullbackOn.{w} hA).obj X) :
    unitScalarOn hA Y ((unitLinearPairPullbackOn.{w} hA).map φ ℓ) =
      ((algebraRingDiagramOn.{v} Pr.ι).map φ).hom (unitScalarOn hA X ℓ) := rfl

/-- The restriction to `D` of an element of the value of a module-valued functor at the base
object. -/
noncomputable abbrev baseValueOn (F : PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι))
    (z : F.obj b.obj) (X : (Pr.FullSubcategory)ᵒᵖᵒᵖ) : F.obj X :=
  F.map (b.hom X.unop.unop).op.op z

/-- Restricting the restriction of a base element gives the restriction of the base element. -/
lemma baseValueOn_map (F : PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι))
    (z : F.obj b.obj) {X Y : (Pr.FullSubcategory)ᵒᵖᵒᵖ} (φ : X ⟶ Y) :
    F.map φ (baseValueOn b F z X) = baseValueOn b F z Y := by
  rw [← PresheafOfModules.map_comp_apply]
  exact F.congr_map_apply (congrArg (fun f ↦ f.op.op) (BaseAlgebraObject.hom_eq b _)) z

/-- The restriction to `D` of the base element of `φ_A^* V` is the structure map `A → D`. -/
lemma unitLinearOn_baseValueOn (X : (Pr.FullSubcategory)ᵒᵖᵒᵖ) (a : unitPairModule.{v} A) :
    unitLinearOn hA X (baseValueOn b (unitLinearPairPullbackOn.{w} hA) (unitElementOn hA b) X) a =
      algebraMap A (X.unop.unop.obj : Type (max u v)) a.down :=
  AlgHom.commutes _ _

/-- Every element `ℓ` of `φ_A^* V` is `ℓ(1)` times the restriction of the base element. -/
lemma unitScalarOn_smul_baseValueOn (X : (Pr.FullSubcategory)ᵒᵖᵒᵖ)
    (ℓ : (unitLinearPairPullbackOn.{w} hA).obj X) :
    unitScalarOn hA X ℓ • baseValueOn b (unitLinearPairPullbackOn.{w} hA) (unitElementOn hA b) X =
      ℓ := by
  have key : ∀ a : unitPairModule.{v} A,
      unitLinearOn hA X (unitScalarOn hA X ℓ •
        baseValueOn b (unitLinearPairPullbackOn.{w} hA) (unitElementOn hA b) X) a =
        unitLinearOn hA X ℓ a := by
    intro a
    have h2 : unitLinearOn hA X ℓ a = a.down • unitLinearOn hA X ℓ (ULift.up 1) := by
      rw [← LinearMap.map_smul]
      congr 1
      exact ULift.ext _ _ (mul_one a.down).symm
    have h3 : unitLinearOn hA X (unitScalarOn hA X ℓ •
        baseValueOn b (unitLinearPairPullbackOn.{w} hA) (unitElementOn hA b) X) a =
        unitLinearOn hA X ℓ (ULift.up 1) *
          unitLinearOn hA X (baseValueOn b (unitLinearPairPullbackOn.{w} hA)
            (unitElementOn hA b) X) a := rfl
    rw [h3, unitLinearOn_baseValueOn, h2, Algebra.smul_def, mul_comm]
  exact ULift.ext _ _ (LinearMap.ext key)

variable (E : PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι)) (y : E.obj b.obj)

/-- The morphism `φ_A^* V ⟶ E` sending the base element to `y`: `ℓ ↦ ℓ(1) · y|_D`. -/
noncomputable def unitHomOn : unitLinearPairPullbackOn.{w} hA ⟶ E where
  app X := ModuleCat.ofHom (X := (unitLinearPairPullbackOn.{w} hA).obj X) (Y := E.obj X)
    { toFun := fun ℓ ↦ unitScalarOn hA X ℓ • baseValueOn b E y X
      map_add' := fun ℓ ℓ' ↦ add_smul (unitScalarOn hA X ℓ) (unitScalarOn hA X ℓ') _
      map_smul' := fun r ℓ ↦ mul_smul r (unitScalarOn hA X ℓ) _ }
  naturality {X Y} φ := by
    ext ℓ
    change unitScalarOn hA Y ((unitLinearPairPullbackOn.{w} hA).map φ ℓ) • baseValueOn b E y Y =
      E.map φ (unitScalarOn hA X ℓ • baseValueOn b E y X)
    rw [unitScalarOn_map, PresheafOfModules.map_smul, baseValueOn_map]
    rfl

include b in
/-- **`φ_A^* V` is projective** on a domain of algebras with a base object. -/
theorem projective_unitLinearPairPullbackOn : Projective (unitLinearPairPullbackOn.{w} hA) where
  factors {E X} f e he := by
    obtain ⟨y, hy⟩ := PresheafOfModules.surjective_of_epi e b.obj (f.app b.obj (unitElementOn hA b))
    refine ⟨unitHomOn hA b E y, PresheafOfModules.hom_ext fun D ↦ ?_⟩
    ext ℓ
    show e.app D (unitScalarOn hA D ℓ • baseValueOn b E y D) = f.app D ℓ
    have h1 : e.app D (baseValueOn b E y D) =
        f.app D (baseValueOn b (unitLinearPairPullbackOn.{w} hA) (unitElementOn hA b) D) :=
      (PresheafOfModules.naturality_apply e (b.hom D.unop.unop).op.op y).trans
        ((congrArg (fun z ↦ X.map (b.hom D.unop.unop).op.op z) hy).trans
          (PresheafOfModules.naturality_apply f (b.hom D.unop.unop).op.op
            (unitElementOn hA b)).symm)
    calc e.app D (unitScalarOn hA D ℓ • baseValueOn b E y D)
        = unitScalarOn hA D ℓ • e.app D (baseValueOn b E y D) :=
          (e.app D).hom.map_smul (unitScalarOn hA D ℓ) _
      _ = unitScalarOn hA D ℓ •
          f.app D (baseValueOn b (unitLinearPairPullbackOn.{w} hA) (unitElementOn hA b) D) :=
          congrArg (unitScalarOn hA D ℓ • ·) h1
      _ = f.app D (unitScalarOn hA D ℓ •
          baseValueOn b (unitLinearPairPullbackOn.{w} hA) (unitElementOn hA b) D) :=
          ((f.app D).hom.map_smul (unitScalarOn hA D ℓ) _).symm
      _ = f.app D ℓ := congrArg (f.app D) (unitScalarOn_smul_baseValueOn hA b D ℓ)

end UnitProjective

section RetractionValues

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]
  (M : ModuleCat.{w} A)

attribute [local instance] symPairAlgebra pairSymDualAlgebra

/-- The `ε`-coefficient on values is linear over `C ⊂ C[ε]`. -/
lemma dualCoefficientMap_algebraMap_smul (X : AlgebraModulePair.{max u v} A) (c : X.algebra)
    (t : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N) ⊗[A] M) :
    dualCoefficientMap N M X (algebraMap (dualNumberPair X).algebra
        (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N))
        ((dualNumberPairInl X).base c) • t) =
      algebraMap X.algebra (pairSym N X) c • dualCoefficientMap N M X t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul s m =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, dualCoefficientMap_tmul, dualCoefficientMap_tmul,
      dualExpandSnd_algebraMap_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- The `ε`-coefficient on values is natural in the pair. -/
lemma dualCoefficientMap_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (t : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N) ⊗[A] M) :
    dualCoefficientMap N M Y
        (TensorProduct.map (symPairMap N (dualNumberPairMap g)).toLinearMap LinearMap.id t) =
      TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id (dualCoefficientMap N M X t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s m =>
    simp only [TensorProduct.map_tmul, dualCoefficientMap_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_apply, dualExpandSnd_naturality]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

end RetractionValues

section RetractionOn

variable {A : Type u} [CommRing A] {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}
  {N : Type (max u v)} [AddCommGroup N] [Module A N] (h : PairsDomainClosed N Pr Qr)

attribute [local instance] symPairAlgebra pairSymDualAlgebra

attribute [local irreducible] dualNumberPair

/-- A morphism `T^* ψ_N^* M̲ ⟶ ψ_N^* M'̲` on a domain of pairs, from a family of `A`-linear maps
on the values which is linear over the algebra of each pair and natural in the pair. -/
noncomputable def dualScalingSymPairExtensionHomOn {M M' : ModuleCat.{max u v w} A}
    (L : ∀ X : AlgebraModulePair.{max u v} A,
      (SymmetricAlgebra (dualNumberPairFunctor.obj X).algebra
          ((dualNumberPairFunctor.obj X).module ⊗[A] N)) ⊗[A] M →ₗ[A]
        (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M')
    (hL : ∀ (X : AlgebraModulePair.{max u v} A) (c : X.algebra) t,
      L X (algebraMap (dualNumberPairFunctor.obj X).algebra
          (SymmetricAlgebra (dualNumberPairFunctor.obj X).algebra
            ((dualNumberPairFunctor.obj X).module ⊗[A] N))
          (((dualNumberRingHom.{v} A).app (op (op X))).hom c) • t) =
        algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c • L X t)
    (hnat : ∀ {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) t,
      L Y (TensorProduct.map (symPairMap N (dualNumberPairFunctor.map g)).toLinearMap
          LinearMap.id t) =
        TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id (L X t)) :
    (dualScalingOn.{max u v w} h.dualNumberPair_mem).obj (symPairExtensionOn.{w} h M) ⟶
      symPairExtensionOn.{w} h M' where
  app X := ModuleCat.ofHom
    (X := ((dualScalingOn.{max u v w} h.dualNumberPair_mem).obj (symPairExtensionOn.{w} h M)).obj X)
    (Y := (symPairExtensionOn.{w} h M').obj X)
    { toFun := L X.unop.unop.obj
      map_add' := map_add _
      map_smul' := fun c t ↦ hL X.unop.unop.obj c t }
  naturality {X Y} g := by
    ext t
    exact hnat g.unop.unop.hom t

/-- **The `ε`-coefficient retraction** `π : T^* ψ_N^* M̲ ⟶ ψ_N^* M̲` on a domain of pairs. -/
noncomputable def dualRetractionOn (M : ModuleCat.{max u v w} A) :
    (dualScalingOn.{max u v w} h.dualNumberPair_mem).obj (symPairExtensionOn.{w} h M) ⟶
      symPairExtensionOn.{w} h M :=
  dualScalingSymPairExtensionHomOn.{w} h (dualCoefficientMap N M)
    (fun X c t ↦ (dualCoefficientMap_algebraMap_smul N M X c t :))
    (fun g t ↦ (dualCoefficientMap_naturality N M g t :))

/-- **`π` is a retraction of `p ≫ τ`** on `ψ_N^* M̲`, on a domain of pairs. -/
theorem dualScalingInlOn_comp_epsOn_comp_retractionOn (M : ModuleCat.{max u v w} A) :
    (dualScalingInlOn.{max u v w} h.dualNumberPair_mem).app (symPairExtensionOn.{w} h M) ≫
        (dualScalingEpsOn.{max u v w} h.dualNumberPair_mem).app (symPairExtensionOn.{w} h M) ≫
          dualRetractionOn.{w} h M =
      𝟙 _ := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  ext t
  exact (dualCoefficientMap_eps_inl N M X.unop.unop.obj t :)

/-- **`a ≫ π` is the weight-one projection** `Π` of `ψ_N^* M̲`, on a domain of pairs. -/
theorem dualScalingInrOn_comp_retractionOn (M : ModuleCat.{max u v w} A) :
    (dualScalingInrOn.{max u v w} h.dualNumberPair_mem).app (symPairExtensionOn.{w} h M) ≫
        dualRetractionOn.{w} h M =
      pairsWeightOneProjectionOn.{w} h M := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  ext t
  exact (dualCoefficientMap_inr N M X.unop.unop.obj t :)

end RetractionOn

section ExtVanishingOn

variable {A : Type u} [CommRing A] {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}

open CategoryTheory.Abelian

/-- **`Ext^{n+1}(V, ψ_A^* G) = 0`** on a domain of pairs, for the rank-one free module `A` and
every module-valued functor `G` on the allowed algebras. -/
theorem subsingleton_ext_tautologicalPairModuleOn_unit
    (hA : PairsDomainClosed (unitPairModule.{v} A) Pr Qr) (b : BaseAlgebraObject.{v} Pr.ι)
    [EnoughInjectives (PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι))]
    [HasExt.{t} (PresheafOfModules.{max u v w} (pairRingDiagramOn Qr))]
    [HasExt.{t'} (PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι))]
    (G : PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι)) (n : ℕ) :
    Subsingleton (Ext.{t} (tautologicalPairModuleOn.{w} Qr)
      ((PresheafOfModules.pushforward.{max u v w} (symPairRingHomOn hA)).obj G) (n + 1)) := by
  have : Projective (unitLinearPairPullbackOn.{w} hA) := projective_unitLinearPairPullbackOn hA b
  have : Subsingleton (Ext.{t'} (unitLinearPairPullbackOn.{w} hA) G (n + 1)) :=
    Ext.subsingleton_of_projective _ _ n
  exact (Stacks.ExtAdjunction.extMap_bijective (pairsPushforwardAdjunctionOn.{max u v w} hA)
    (tautologicalPairModuleOn.{w} Qr) G (n + 1)).injective.subsingleton

end ExtVanishingOn

section RepresentationOn

variable {A : Type u} [CommRing A] {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}
  {N : Type (max u v)} [AddCommGroup N] [Module A N] (h : PairsDomainClosed N Pr Qr)

/-- A module-valued functor `L` on the allowed algebras with natural identifications
`L(B) ≃ Hom_A(N, B)` is the restriction `φ_N^* V` of the tautological functor on the allowed
pairs. -/
noncomputable def linearPairPullbackIsoOn
    (L : PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι))
    (e : ∀ X : Pr.FullSubcategory,
      L.obj (op (op X)) ≃ₗ[(X.obj : Type (max u v))] (N →ₗ[A] (X.obj : Type (max u v))))
    (he : ∀ (X Y : Pr.FullSubcategory) (f : X ⟶ Y) (x : L.obj (op (op X))),
      e Y (L.map f.op.op x) = (Pr.ι.map f).hom.toLinearMap.comp (e X x)) :
    L ≅ (PresheafOfModules.pushforward.{max u v w} (linearPairRingHomOn h)).obj
      (tautologicalPairModuleOn.{w} Qr) :=
  PresheafOfModules.isoMk
    (fun X ↦ LinearEquiv.toModuleIso
      { toFun := fun x ↦ ULift.up (e X.unop.unop x)
        invFun := fun y ↦ (e X.unop.unop).symm y.down
        left_inv := fun x ↦ (e X.unop.unop).symm_apply_apply x
        right_inv := fun y ↦ congrArg ULift.up ((e X.unop.unop).apply_symm_apply y.down)
        map_add' := fun x y ↦ congrArg ULift.up ((e X.unop.unop).map_add x y)
        map_smul' := fun r x ↦ congrArg ULift.up ((e X.unop.unop).map_smul r x) })
    (fun X Y f ↦ by
      ext x
      exact congrArg ULift.up (he X.unop.unop Y.unop.unop f.unop.unop x))

end RepresentationOn

section WeightOneExtOn

variable {A : Type u} [CommRing A] {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}
  {N : Type (max u v)} [AddCommGroup N] [Module A N] (h : PairsDomainClosed N Pr Qr)

open CategoryTheory.Abelian

/-- **Classes out of `V` see only the weight-one part of `ψ_N^* M̲`**, on a domain of pairs:
for every `ξ ∈ Ext^n(V, ψ_N^* M̲)`, `ξ ∘ Π = ξ`. -/
theorem ext_comp_pairsWeightOneProjectionOn
    [inst : HasExt.{t} (PresheafOfModules.{max u v w} (pairRingDiagramOn Qr))]
    [EnoughInjectives (PresheafOfModules.{max u v w} (pairRingDiagramOn Qr))]
    (M : ModuleCat.{max u v w} A) (n : ℕ)
    (ξ : @Ext _ _ _ inst (tautologicalPairModuleOn.{w} Qr) (symPairExtensionOn.{w} h M) n) :
    @Ext.comp _ _ _ inst _ _ _ _ _ ξ
      (@Ext.mk₀ _ _ _ inst _ _ (pairsWeightOneProjectionOn.{w} h M)) _ (add_zero n) = ξ := by
  have hX := dualScalingInrOn_app_tautological.{w} h.dualNumberPair_mem
  have hπ : (dualScalingInlOn.{max u v w} h.dualNumberPair_mem).app (symPairExtensionOn.{w} h M) ≫
        (dualScalingEpsOn.{max u v w} h.dualNumberPair_mem).app (symPairExtensionOn.{w} h M) ≫
          dualRetractionOn.{w} h M = 𝟙 _ := dualScalingInlOn_comp_epsOn_comp_retractionOn h M
  have hξ := @Stacks.ExtFunctorial.comp_mk₀_eq_self_of_app_eq_comp _ _ _ inst _
    (dualScalingOn.{max u v w} h.dualNumberPair_mem) _ _ _
    (dualScalingInlOn.{max u v w} h.dualNumberPair_mem)
    (dualScalingInrOn.{max u v w} h.dualNumberPair_mem)
    (dualScalingEpsOn.{max u v w} h.dualNumberPair_mem) _ hX _ (dualRetractionOn.{w} h M) hπ n ξ
  rwa [dualScalingInrOn_comp_retractionOn] at hξ

/-- **`Ext^{n+1}(V, ψ_N^* M̲) = 0`** on a domain of pairs with a base object of algebras. -/
theorem subsingleton_ext_tautologicalPairModuleOn_symPairExtensionOn
    (hA : PairsDomainClosed (unitPairModule.{v} A) Pr Qr) (b : BaseAlgebraObject.{v} Pr.ι)
    [EnoughInjectives (PresheafOfModules.{max u v w} (pairRingDiagramOn Qr))]
    [EnoughInjectives (PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι))]
    [HasExt.{t} (PresheafOfModules.{max u v w} (pairRingDiagramOn Qr))]
    [HasExt.{t'} (PresheafOfModules.{max u v w} (algebraRingDiagramOn.{v} Pr.ι))]
    (M : ModuleCat.{max u v w} A) (n : ℕ) :
    Subsingleton (Ext.{t} (tautologicalPairModuleOn.{w} Qr) (symPairExtensionOn.{w} h M)
      (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  have := subsingleton_ext_tautologicalPairModuleOn_unit.{t, t'} hA b
    ((moduleExtensionFunctorOn.{max u v w, v} Pr.ι).obj (ModuleCat.of A (N ⊗[A] M))) n
  have h0 : ξ.comp (Ext.mk₀ (pairsWeightOneOutOn.{w} h hA M)) (add_zero (n + 1)) = 0 :=
    Subsingleton.elim _ _
  rw [← ext_comp_pairsWeightOneProjectionOn h M (n + 1) ξ,
    ← pairsWeightOneOutOn_comp_inOn h hA M, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, h0, Ext.zero_comp]

end WeightOneExtOn

section Assembly

variable {A : Type u} [CommRing A] {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)}

open CategoryTheory.Abelian

/-- Let `Pr` be a full subcategory of `A`-algebras with a base object, and `Qr` a full
subcategory of pairs `(C, V)` such that, for every finitely presented `A`-module `N`, the
adjunction `ψ_N ⊣ φ_N` restricts to `Pr` and `Qr` and `Qr` is closed under the dual-number pairs
(`AdequateFunctor.PairsDomainClosed`). If the module-valued functors on `Pr` and on `Qr` have
enough injectives, then for every linearly adequate functor `L` on `Pr` and every `A`-module `M`,
`Ext^i(L, M̲) = 0` for `i > 0`. -/
theorem subsingleton_zExt_isLinearlyAdequate_moduleExtensionOn
    (b : BaseAlgebraObject.{v} Pr.ι)
    (hcl : ∀ (N : Type (max u v)) [AddCommGroup N] [Module A N] [Module.FinitePresentation A N],
      PairsDomainClosed N Pr Qr)
    [EnoughInjectives (PresheafOfModules.{max u v w} (pairRingDiagramOn Qr))]
    [EnoughInjectives (ModuleValuedFunctorOn.{max u v w} Pr.ι)]
    [HasDerivedCategory.{t} (ModuleValuedFunctorOn.{max u v w} Pr.ι)]
    (L : ModuleValuedFunctorOn.{max u v w} Pr.ι) (hL : IsLinearlyAdequate.{max u v w, v} Pr.ι L)
    (M : ModuleCat.{max u v w} A) (i : ℤ) (hi : 0 < i) :
    Subsingleton (Abelian.zExt L ((moduleExtensionFunctorOn.{max u v w, v} Pr.ι).obj M) i) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = ((n + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
  let : HasExt.{t} (ModuleValuedFunctorOn.{max u v w} Pr.ι) := hasExt_of_hasDerivedCategory _
  let := HasExt.standard (PresheafOfModules.{max u v w} (pairRingDiagramOn Qr))
  obtain ⟨N, hNadd, hNmod, hNfp, e, he⟩ :=
    LaurentDomain.exists_linearRepresentation_smallCarrier.{u, v, w} b L hL
  have : Module.FinitePresentation A (unitPairModule.{v} A) :=
    Module.FinitePresentation.of_equiv (ULift.moduleEquiv.symm : A ≃ₗ[A] unitPairModule.{v} A)
  have h : PairsDomainClosed N Pr Qr := hcl N
  have hA : PairsDomainClosed (unitPairModule.{v} A) Pr Qr := hcl _
  let iso := linearPairPullbackIsoOn.{w} h L e he
  have := subsingleton_ext_tautologicalPairModuleOn_symPairExtensionOn h hA b M n
  have : Subsingleton (Ext.{t} ((PresheafOfModules.pushforward.{max u v w}
      (linearPairRingHomOn h)).obj (tautologicalPairModuleOn.{w} Qr))
      ((moduleExtensionFunctorOn.{max u v w, v} Pr.ι).obj M) (n + 1)) :=
    (Stacks.ExtAdjunction.extMap_bijective (pairsPushforwardAdjunctionOn.{max u v w} h)
      (tautologicalPairModuleOn.{w} Qr) _ (n + 1)).surjective.subsingleton
  have : Subsingleton (Ext.{t} L ((moduleExtensionFunctorOn.{max u v w, v} Pr.ι).obj M)
      (n + 1)) :=
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso iso.hom (n + 1)).surjective.subsingleton
  exact (Ext.homEquiv.{t, t} (X := L) (Y := (moduleExtensionFunctorOn.{max u v w, v} Pr.ι).obj M)
    (n := n + 1)).subsingleton_congr.mp inferInstance

end Assembly

end AdequateFunctor

end
