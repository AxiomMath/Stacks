module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import StacksFrontier.Algebra.Module.Adequate.Tangent
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.BaseChangeExt
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.DualScalingPair
public import StacksFrontier.Algebra.Module.Adequate.Splitting06V7Large

/-!
# Module-valued functors on pairs and the transfer of `Ext` out of `Hom_A(N, -)`

A *pair* over a ring `A` is an `A`-algebra `C` together with a `C`-module `V`
(`AdequateFunctor.AlgebraModulePair`). Module-valued functors on pairs are the presheaves of
modules over the ring diagram `(C, V) ↦ C`. Among them is the tautological one, `(C, V) ↦ V`.

For an `A`-module `N`, the functor `φ_N : D ↦ (D, Hom_A(N, D))` from `A`-algebras to pairs has
the left adjoint `ψ_N : (C, V) ↦ Sym_C(V ⊗_A N)`. Precomposition gives an adjunction
`φ_N^* ⊣ ψ_N^*` between module-valued functors on pairs and module-valued functors on
`A`-algebras, with both functors exact. Hence, for every module-valued functor `G` on
`A`-algebras, `Ext^n(V, ψ_N^* G) ≃ Ext^n(φ_N^* V, G)`, where `φ_N^* V` is the functor
`D ↦ Hom_A(N, D)` and `ψ_N^* G` is `(C, V) ↦ G(Sym_C(V ⊗_A N))`.

## Main definitions

* `AdequateFunctor.pairRingDiagram`: the ring diagram `(C, V) ↦ C` on pairs.
* `AdequateFunctor.PairModuleValuedFunctor`: module-valued functors on pairs.
* `AdequateFunctor.tautologicalPairModule`: the module-valued functor `(C, V) ↦ V`.
* `AdequateFunctor.linearPairFunctor`: the functor `φ_N : D ↦ (D, Hom_A(N, D))`.
* `AdequateFunctor.symPairFunctor`: its left adjoint `ψ_N : (C, V) ↦ Sym_C(V ⊗_A N)`.
* `AdequateFunctor.pairsPushforwardAdjunction`: the adjunction `φ_N^* ⊣ ψ_N^*`.

## Main results

* `AdequateFunctor.extMap_pairsPushforwardAdjunction_bijective`: the transfer
  `Ext^n(F, ψ_N^* G) ≃ Ext^n(φ_N^* F, G)`.

## Implementation notes

The `A`-algebra structure on `Sym_C(V ⊗_A N)` is the composite `A → C → Sym_C(V ⊗_A N)`. It is
provided by `AdequateFunctor.symPairAlgebra` as a local instance only: Mathlib's
`SymmetricAlgebra` carries no such instance, and a global one would clash with Mathlib's own
algebra structure when `C` is `A` itself.

## References

* [Stacks Project, Tag 06ZH](https://stacks.math.columbia.edu/tag/06ZH)
* [Stacks Project, Tag 06ZG](https://stacks.math.columbia.edu/tag/06ZG)
-/

@[expose] public section

universe t t' w v u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AdequateFunctor

section Pairs

variable (A : Type u) [CommRing A]

/-- The ring diagram `(C, V) ↦ C` on pairs of an `A`-algebra and a module over it. -/
abbrev pairRingDiagram : ((AlgebraModulePair.{max u v} A)ᵒᵖ)ᵒᵖ ⥤ RingCat.{max u v} where
  obj X := RingCat.of X.unop.unop.algebra
  map f := RingCat.ofHom f.unop.unop.base.toRingHom

set_option linter.checkUnivs false in
/-- Module-valued functors on pairs of an `A`-algebra and a module over it. -/
abbrev PairModuleValuedFunctor := PresheafOfModules.{w} (pairRingDiagram.{v} A)

/-- The tautological module-valued functor `(C, V) ↦ V` on pairs, with values in the universe
of the pairs. -/
noncomputable def tautologicalPairModuleSmall :
    PresheafOfModules.{max u v} (pairRingDiagram.{v} A) where
  obj X := ModuleCat.of X.unop.unop.algebra X.unop.unop.module
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (RingCat.Hom.hom ((pairRingDiagram.{v} A).map f))).obj
      (ModuleCat.of Y.unop.unop.algebra Y.unop.unop.module))
    { toFun := fun x => f.unop.unop.linear x
      map_add' := fun x y => map_add f.unop.unop.linear x y
      map_smul' := fun r x => f.unop.unop.linear.map_smulₛₗ r x }

/-- The tautological module-valued functor `(C, V) ↦ V` on pairs. -/
noncomputable abbrev tautologicalPairModule :
    PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A :=
  (presheafOfModulesUliftFunctor.{max (u + 1) (v + 1) w} (pairRingDiagram.{v} A)).obj
    (tautologicalPairModuleSmall.{v} A)

end Pairs

section SymLift

variable {A : Type u} [CommRing A]

/-- The `A`-algebra structure `A → C → Sym_C(W)` on the symmetric algebra of a module `W` over an
`A`-algebra `C`. Used as a local instance only, see the implementation notes. -/
@[instance_reducible]
noncomputable def symPairAlgebra (C : Type*) [CommRing C] [Algebra A C] (W : Type*)
    [AddCommGroup W] [Module C W] : Algebra A (SymmetricAlgebra C W) :=
  ((algebraMap C (SymmetricAlgebra C W)).comp (algebraMap A C)).toAlgebra

attribute [local instance] symPairAlgebra

/-- `A → C → Sym_C(W)` is a scalar tower. -/
instance symPairAlgebra_isScalarTower (C : Type*) [CommRing C] [Algebra A C] (W : Type*)
    [AddCommGroup W] [Module C W] : IsScalarTower A C (SymmetricAlgebra C W) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The structure map `C → Sym_C(W)` as a map of `A`-algebras. -/
noncomputable def symAlgebraMap (C : Type*) [CommRing C] [Algebra A C] (W : Type*)
    [AddCommGroup W] [Module C W] : C →ₐ[A] SymmetricAlgebra C W :=
  { algebraMap C (SymmetricAlgebra C W) with commutes' := fun _ => rfl }

variable {C : Type*} [CommRing C] [Algebra A C] {W : Type*} [AddCommGroup W] [Module C W]
  {D : Type*} [CommRing D] [Algebra A D]

/-- The `A`-algebra map `Sym_C(W) → D` extending an `A`-algebra map `f : C → D` and an
`f`-semilinear map `W → D`. -/
noncomputable def symLift (f : C →ₐ[A] D) (ℓ : W →ₛₗ[f.toRingHom] D) :
    SymmetricAlgebra C W →ₐ[A] D :=
  letI : Algebra C D := f.toRingHom.toAlgebra
  haveI : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  (SymmetricAlgebra.lift (R := C) (M := W) (A := D)
    { toFun := ℓ
      map_add' := ℓ.map_add
      map_smul' := fun c x => ℓ.map_smulₛₗ c x }).restrictScalars A

/-- `symLift f ℓ` restricts to `f` on `C`. -/
@[simp]
lemma symLift_algebraMap (f : C →ₐ[A] D) (ℓ : W →ₛₗ[f.toRingHom] D) (c : C) :
    symLift f ℓ (algebraMap C (SymmetricAlgebra C W) c) = f c := by
  let : Algebra C D := f.toRingHom.toAlgebra
  exact (SymmetricAlgebra.lift (R := C) (M := W) (A := D) _).commutes c

/-- `symLift f ℓ` restricts to `ℓ` on `W`. -/
@[simp]
lemma symLift_ι (f : C →ₐ[A] D) (ℓ : W →ₛₗ[f.toRingHom] D) (x : W) :
    symLift f ℓ (SymmetricAlgebra.ι C W x) = ℓ x := by
  let : Algebra C D := f.toRingHom.toAlgebra
  exact SymmetricAlgebra.lift_ι_apply (R := C) (M := W) (A := D) _ x

/-- Two `A`-algebra maps out of `Sym_C(W)` agreeing on `C` and on `W` are equal. -/
lemma symAlgHom_ext {φ ψ : SymmetricAlgebra C W →ₐ[A] D}
    (hC : ∀ c, φ (algebraMap C _ c) = ψ (algebraMap C _ c))
    (hW : ∀ x, φ (SymmetricAlgebra.ι C W x) = ψ (SymmetricAlgebra.ι C W x)) : φ = ψ := by
  ext a
  induction a using SymmetricAlgebra.induction with
  | algebraMap c => exact hC c
  | ι x => exact hW x
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end SymLift

section Adjunction

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]

attribute [local instance] symPairAlgebra

/-- The pair `(D, Hom_A(N, D))`. -/
abbrev linearPair (D : CommAlgCat.{max u v} A) : AlgebraModulePair.{max u v} A :=
  { algebra := D, module := N →ₗ[A] D }

/-- The functor `φ_N : D ↦ (D, Hom_A(N, D))` from `A`-algebras to pairs. -/
noncomputable abbrev linearPairFunctor :
    CommAlgCat.{max u v} A ⥤ AlgebraModulePair.{max u v} A where
  obj D := linearPair N D
  map {D D'} h :=
    { base := h.hom
      linear :=
        { toFun := fun g => h.hom.toLinearMap ∘ₗ g
          map_add' := fun g g' => LinearMap.comp_add _ _ _
          map_smul' := fun d g => LinearMap.ext fun n => by
            change h.hom (d * g n) = h.hom d * h.hom (g n)
            exact map_mul _ _ _ } }
  map_id D := rfl
  map_comp f g := rfl

/-- The `A`-algebra `Sym_C(V ⊗_A N)` attached to a pair `(C, V)`. -/
noncomputable abbrev symPairObj (X : AlgebraModulePair.{max u v} A) : CommAlgCat.{max u v} A :=
  CommAlgCat.of A (SymmetricAlgebra X.algebra (X.module ⊗[A] N))

/-- An `f`-semilinear map `V → Hom_A(N, D)` as the `f`-semilinear map `V ⊗_A N → D`. -/
noncomputable def pairTensorLift {X : AlgebraModulePair.{max u v} A} {D : CommAlgCat.{max u v} A}
    (p : X ⟶ linearPair N D) :
    X.module ⊗[A] N →ₛₗ[p.base.toRingHom] D :=
  { toFun := TensorProduct.lift
      { toFun := p.linear
        map_add' := p.linear.map_add
        map_smul' := fun a x => by
          rw [← algebraMap_smul X.algebra a x, p.linear.map_smulₛₗ]
          ext n
          change p.base (algebraMap A X.algebra a) * _ = a • _
          rw [AlgHom.commutes, Algebra.smul_def] }
    map_add' := map_add _
    map_smul' := fun c t => by
      induction t using TensorProduct.inductionOn with
      | tmul x n =>
        rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        change p.linear (c • x) n = p.base c * p.linear x n
        rw [p.linear.map_smulₛₗ]
        rfl
      | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add] }

/-- `pairTensorLift N p` sends `x ⊗ n` to `p.linear x n`. -/
lemma pairTensorLift_tmul {X : AlgebraModulePair.{max u v} A} {D : CommAlgCat.{max u v} A}
    (p : X ⟶ linearPair N D) (x : X.module) (n : N) :
    pairTensorLift N p (x ⊗ₜ n) = p.linear x n := rfl

/-- The adjunction bijection `Hom(Sym_C(V ⊗_A N), D) ≃ Hom((C, V), (D, Hom_A(N, D)))`. -/
noncomputable def symPairHomEquiv (X : AlgebraModulePair.{max u v} A) (D : CommAlgCat.{max u v} A) :
    (symPairObj N X ⟶ D) ≃ (X ⟶ linearPair N D) where
  toFun φ :=
    { base := φ.hom.comp (symAlgebraMap X.algebra (X.module ⊗[A] N))
      linear :=
        { toFun := fun x =>
            (φ.hom.toLinearMap ∘ₗ ((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N)).restrictScalars
              A)) ∘ₗ TensorProduct.mk A X.module N x
          map_add' := fun x y => LinearMap.ext fun n => by
            change φ.hom (SymmetricAlgebra.ι _ _ ((x + y) ⊗ₜ n)) =
              φ.hom (SymmetricAlgebra.ι _ _ (x ⊗ₜ n)) + φ.hom (SymmetricAlgebra.ι _ _ (y ⊗ₜ n))
            rw [TensorProduct.add_tmul, map_add, map_add]
          map_smul' := fun c x => LinearMap.ext fun n => by
            change φ.hom (SymmetricAlgebra.ι _ _ ((c • x) ⊗ₜ n)) =
              φ.hom (algebraMap X.algebra _ c) * φ.hom (SymmetricAlgebra.ι _ _ (x ⊗ₜ n))
            rw [← TensorProduct.smul_tmul', map_smul, ← map_mul]
            exact congrArg φ.hom (Algebra.smul_def c _) } }
  invFun p := CommAlgCat.ofHom (symLift p.base (pairTensorLift N p))
  left_inv φ := by
    refine CommAlgCat.hom_ext (symAlgHom_ext (fun c => ?_) (fun t => ?_))
    · exact symLift_algebraMap _ _ c
    · refine (symLift_ι _ _ t).trans ?_
      induction t using TensorProduct.inductionOn with
      | tmul x n => rfl
      | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  right_inv p := by
    refine AlgebraModulePair.Hom.ext _ _ (AlgHom.ext fun c => symLift_algebraMap _ _ c)
      (fun x => ?_)
    exact LinearMap.ext fun n => symLift_ι _ _ _

/-- The bijection `symPairHomEquiv` is natural in the algebra `D`. -/
lemma symPairHomEquiv_naturality (X : AlgebraModulePair.{max u v} A)
    (D D' : CommAlgCat.{max u v} A) (g : D ⟶ D') (h : symPairObj N X ⟶ D) :
    symPairHomEquiv N X D' (h ≫ g) = symPairHomEquiv N X D h ≫ (linearPairFunctor N).map g :=
  AlgebraModulePair.Hom.ext _ _ rfl fun _ => LinearMap.ext fun _ => by
    dsimp [symPairHomEquiv, linearPairFunctor]
    rfl

/-- `(symPairHomEquiv N X D).symm p` restricts to `p.base` on `C`. -/
lemma symPairHomEquiv_symm_algebraMap (X : AlgebraModulePair.{max u v} A)
    (D : CommAlgCat.{max u v} A) (p : X ⟶ linearPair N D) (c : X.algebra) :
    ((symPairHomEquiv N X D).symm p).hom
      (algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c) = p.base c :=
  symLift_algebraMap _ _ c

/-- The functor `ψ_N : (C, V) ↦ Sym_C(V ⊗_A N)`, left adjoint to `φ_N`. -/
noncomputable def symPairFunctor : AlgebraModulePair.{max u v} A ⥤ CommAlgCat.{max u v} A :=
  Adjunction.leftAdjointOfEquiv (G := linearPairFunctor N) (symPairHomEquiv N)
    (symPairHomEquiv_naturality N)

/-- The adjunction `ψ_N ⊣ φ_N`. -/
noncomputable def symPairAdjunction : symPairFunctor (A := A) N ⊣ linearPairFunctor N :=
  Adjunction.adjunctionOfEquivLeft (G := linearPairFunctor N) (symPairHomEquiv N)
    (symPairHomEquiv_naturality N)

/-- The identity ring maps `D = D`, comparing the ring diagram of `A`-algebras with that of
pairs along `φ_N`. -/
noncomputable def linearPairRingHom :
    algebraRingDiagram.{v} A ⟶
      (linearPairFunctor.{v, u} (A := A) N).op.op ⋙ pairRingDiagram.{v} A where
  app X := RingCat.ofHom (RingHom.id X.unop.unop)
  naturality := by
    intro X Y g
    ext x
    rfl

/-- The structure maps `C → Sym_C(V ⊗_A N)`, comparing the ring diagram of pairs with that of
`A`-algebras along `ψ_N`. -/
noncomputable def symPairRingHom :
    pairRingDiagram.{v} A ⟶
      (symPairFunctor.{v, u} (A := A) N).op.op ⋙ algebraRingDiagram.{v} A where
  app X := RingCat.ofHom (algebraMap X.unop.unop.algebra
    (SymmetricAlgebra X.unop.unop.algebra (X.unop.unop.module ⊗[A] N)))
  naturality := by
    intro X Y g
    refine RingCat.hom_ext (RingHom.ext fun (x : X.unop.unop.algebra) => ?_)
    exact (symPairHomEquiv_symm_algebraMap N X.unop.unop (symPairObj N Y.unop.unop)
      (g.unop.unop ≫ symPairHomEquiv N _ (symPairObj N _) (𝟙 _)) x).symm

/-- On rings, the counit of the opposite adjunction `φ_N.op ⊣ ψ_N.op` is the composite of the
comparison maps `symPairRingHom` and `linearPairRingHom`. -/
lemma pairsRingDiagram_counit (Y : (AlgebraModulePair.{max u v} A)ᵒᵖ) :
    (pairRingDiagram.{v} A).map ((symPairAdjunction.{v, u} (A := A) N).op.counit.app Y).op =
      (symPairRingHom.{v, u} (A := A) N).app (op Y) ≫
        (linearPairRingHom.{v, u} (A := A) N).app
          (op ((symPairFunctor.{v, u} (A := A) N).op.obj Y)) := by
  ext x
  rfl

/-- On rings, the comparison maps `linearPairRingHom` and `symPairRingHom` followed by the unit of
the opposite adjunction `φ_N.op ⊣ ψ_N.op` compose to the identity. -/
lemma pairsRingDiagram_unit (X : (CommAlgCat.{max u v} A)ᵒᵖ) :
    (linearPairRingHom.{v, u} (A := A) N).app (op X) ≫
        (symPairRingHom.{v, u} (A := A) N).app
            (op ((linearPairFunctor.{v, u} (A := A) N).op.obj X)) ≫
          (algebraRingDiagram.{v} A).map ((symPairAdjunction.{v, u} (A := A) N).op.unit.app X).op =
      𝟙 _ :=
  RingCat.hom_ext (RingHom.ext fun (x : X.unop) =>
    symPairHomEquiv_symm_algebraMap N (linearPair N X.unop) X.unop (𝟙 _) x)

/-- **The adjunction `φ_N^* ⊣ ψ_N^*`.** Restricting a module-valued functor on pairs along
`φ_N : D ↦ (D, Hom_A(N, D))` is left adjoint to `G ↦ ((C, V) ↦ G(Sym_C(V ⊗_A N)))`. -/
noncomputable def pairsPushforwardAdjunction :
    PresheafOfModules.pushforward.{w} (linearPairRingHom.{v, u} (A := A) N) ⊣
      PresheafOfModules.pushforward.{w} (symPairRingHom.{v, u} (A := A) N) :=
  presheafPushforwardAdjunction (symPairAdjunction.{v, u} (A := A) N).op
    (linearPairRingHom.{v, u} (A := A) N) (symPairRingHom.{v, u} (A := A) N)
    (pairsRingDiagram_counit.{v, u} (A := A) N) (pairsRingDiagram_unit.{v, u} (A := A) N)

end Adjunction

section Domain

/-! ### Restriction to a domain of algebras

For a full subcategory `Pr` of `A`-algebras (for instance the algebras of a big site) and a full
subcategory `Qr` of pairs, the adjunction `ψ_N ⊣ φ_N` restricts as soon as `φ_N` maps `Pr` into
`Qr` and `ψ_N` maps `Qr` into `Pr`. The closure conditions are recorded one by one in
`AdequateFunctor.PairsDomainClosed`, together with closure of `Qr` under the dual-number pairs
`(C[ε], V ⊕ εV)` (`AdequateFunctor.dualNumberPair`). -/

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]

attribute [local instance] symPairAlgebra

/-- The closure conditions under which the adjunction `ψ_N ⊣ φ_N` restricts to a domain `Pr` of
algebras and a domain `Qr` of pairs, and `Qr` contains the dual-number pairs of its objects. -/
structure PairsDomainClosed (Pr : ObjectProperty (CommAlgCat.{max u v} A))
    (Qr : ObjectProperty (AlgebraModulePair.{max u v} A)) : Prop where
  /-- `φ_N(D) = (D, Hom_A(N, D))` is an allowed pair for every allowed algebra `D`. -/
  linearPair_mem : ∀ D, Pr D → Qr (linearPair N D)
  /-- `ψ_N(C, V) = Sym_C(V ⊗_A N)` is an allowed algebra for every allowed pair `(C, V)`. -/
  symPairObj_mem : ∀ X, Qr X → Pr (symPairObj N X)
  /-- The dual-number pair `(C[ε], V ⊕ εV)` of an allowed pair is allowed. -/
  dualNumberPair_mem : ∀ X, Qr X → Qr (dualNumberPair X)

variable {N} {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)} (h : PairsDomainClosed N Pr Qr)

/-- The ring diagram `(C, V) ↦ C` on a domain of pairs. -/
abbrev pairRingDiagramOn (Qr : ObjectProperty (AlgebraModulePair.{max u v} A)) :
    ((Qr.FullSubcategory)ᵒᵖ)ᵒᵖ ⥤ RingCat.{max u v} :=
  Qr.ι.op.op ⋙ pairRingDiagram.{v} A

/-- `φ_N` on the domains. -/
noncomputable abbrev linearPairFunctorOn : Pr.FullSubcategory ⥤ Qr.FullSubcategory :=
  Qr.lift (Pr.ι ⋙ linearPairFunctor.{v, u} N) fun D => h.linearPair_mem D.obj D.property

/-- `ψ_N` on the domains. -/
noncomputable abbrev symPairFunctorOn : Qr.FullSubcategory ⥤ Pr.FullSubcategory :=
  Pr.lift (Qr.ι ⋙ symPairFunctor.{v, u} N) fun X => h.symPairObj_mem X.obj X.property

/-- The adjunction `ψ_N ⊣ φ_N` on the domains: the unit and counit of `ψ_N ⊣ φ_N`. -/
noncomputable def symPairAdjunctionOn : symPairFunctorOn h ⊣ linearPairFunctorOn h where
  unit :=
    { app X := ObjectProperty.homMk ((symPairAdjunction.{v, u} (A := A) N).unit.app X.obj)
      naturality _ _ f := ObjectProperty.hom_ext _
        ((symPairAdjunction.{v, u} (A := A) N).unit.naturality f.hom) }
  counit :=
    { app D := ObjectProperty.homMk ((symPairAdjunction.{v, u} (A := A) N).counit.app D.obj)
      naturality _ _ f := ObjectProperty.hom_ext _
        ((symPairAdjunction.{v, u} (A := A) N).counit.naturality f.hom) }
  left_triangle_components X := ObjectProperty.hom_ext _
    ((symPairAdjunction.{v, u} (A := A) N).left_triangle_components X.obj)
  right_triangle_components D := ObjectProperty.hom_ext _
    ((symPairAdjunction.{v, u} (A := A) N).right_triangle_components D.obj)

/-- The identity ring maps along `φ_N` on the domains. -/
noncomputable def linearPairRingHomOn :
    algebraRingDiagramOn.{v} Pr.ι ⟶ (linearPairFunctorOn h).op.op ⋙ pairRingDiagramOn Qr :=
  Functor.whiskerLeft Pr.ι.op.op (linearPairRingHom.{v, u} N)

/-- The structure maps `C → Sym_C(V ⊗_A N)` along `ψ_N` on the domains. -/
noncomputable def symPairRingHomOn :
    pairRingDiagramOn Qr ⟶ (symPairFunctorOn h).op.op ⋙ algebraRingDiagramOn.{v} Pr.ι :=
  Functor.whiskerLeft Qr.ι.op.op (symPairRingHom.{v, u} N)

/-- On rings, the counit of the opposite adjunction `φ_N.op ⊣ ψ_N.op` on the domains is the
composite of the comparison maps `symPairRingHomOn` and `linearPairRingHomOn`. -/
lemma pairsRingDiagramOn_counit (Y : (Qr.FullSubcategory)ᵒᵖ) :
    (pairRingDiagramOn Qr).map ((symPairAdjunctionOn h).op.counit.app Y).op =
      (symPairRingHomOn h).app (op Y) ≫
        (linearPairRingHomOn h).app (op ((symPairFunctorOn h).op.obj Y)) := by
  ext x
  rfl

/-- On rings, the comparison maps `linearPairRingHomOn` and `symPairRingHomOn` followed by the unit
of the opposite adjunction `φ_N.op ⊣ ψ_N.op` on the domains compose to the identity. -/
lemma pairsRingDiagramOn_unit (X : (Pr.FullSubcategory)ᵒᵖ) :
    (linearPairRingHomOn h).app (op X) ≫
        (symPairRingHomOn h).app (op ((linearPairFunctorOn h).op.obj X)) ≫
          (algebraRingDiagramOn.{v} Pr.ι).map ((symPairAdjunctionOn h).op.unit.app X).op =
      𝟙 _ :=
  pairsRingDiagram_unit N (op X.unop.obj)

/-- **The adjunction `φ_N^* ⊣ ψ_N^*` on the domains.** -/
noncomputable def pairsPushforwardAdjunctionOn :
    PresheafOfModules.pushforward.{w} (linearPairRingHomOn h) ⊣
      PresheafOfModules.pushforward.{w} (symPairRingHomOn h) :=
  presheafPushforwardAdjunction (symPairAdjunctionOn h).op (linearPairRingHomOn h)
    (symPairRingHomOn h) (pairsRingDiagramOn_counit h) (pairsRingDiagramOn_unit h)

end Domain

section Representation

variable {A : Type u} [CommRing A]

/-- A module-valued functor `L` with natural identifications `L(B) ≃ Hom_A(N, B)` is the
restriction `φ_N^* V` of the tautological functor on pairs along `φ_N : D ↦ (D, Hom_A(N, D))`. -/
noncomputable def linearPairPullbackIso (N : Type (max u v)) [AddCommGroup N] [Module A N]
    (L : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
    (e : ∀ B : CommAlgCat.{max u v} A, algebraValueLarge L B ≃ₗ[B] (N →ₗ[A] B))
    (he : ∀ (B C : CommAlgCat.{max u v} A) (f : B ⟶ C) (x : algebraValueLarge L B),
      e C (algebraMapValueLarge L f.hom x) = f.hom.toLinearMap.comp (e B x)) :
    L ≅ (PresheafOfModules.pushforward.{max (u + 1) (v + 1) w}
      (linearPairRingHom.{v, u} (A := A) N)).obj (tautologicalPairModule.{w, v} A) :=
  PresheafOfModules.isoMk
    (fun X => LinearEquiv.toModuleIso
      { toFun := fun x => ULift.up (e X.unop.unop x)
        invFun := fun y => (e X.unop.unop).symm y.down
        left_inv := fun x => (e X.unop.unop).symm_apply_apply x
        right_inv := fun y => congrArg ULift.up ((e X.unop.unop).apply_symm_apply y.down)
        map_add' := fun x y => congrArg ULift.up ((e X.unop.unop).map_add x y)
        map_smul' := fun r x => congrArg ULift.up ((e X.unop.unop).map_smul r x) })
    (fun X Y f => by
      ext x
      exact congrArg ULift.up (he X.unop.unop Y.unop.unop f.unop.unop x))

/-- Every linearly adequate module-valued functor is `φ_N^* V` for a finitely presented
`A`-module `N`: the functor `D ↦ Hom_A(N, D)` is the restriction of the tautological functor on
pairs along `φ_N`. -/
theorem exists_iso_linearPairPullback (L : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
    (hL : IsLinearlyAdequate (𝟭 _) L) :
    ∃ (N : Type (max u v)) (_ : AddCommGroup N) (_ : Module A N),
      Module.FinitePresentation A N ∧
      Nonempty (L ≅ (PresheafOfModules.pushforward.{max (u + 1) (v + 1) w}
        (linearPairRingHom.{v, u} (A := A) N)).obj (tautologicalPairModule.{w, v} A)) := by
  obtain ⟨N, hNadd, hNmod, hNfp, e, he⟩ :=
    exists_linearRepresentation_smallCarrier_large.{u, v, max (u + 1) (v + 1) w} L hL
  exact ⟨N, hNadd, hNmod, hNfp, ⟨linearPairPullbackIso.{w, v, u} N L e he⟩⟩

end Representation

section Ext

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]

open Stacks.AlgebraicGeometry.RestrictionExact CategoryTheory.Limits

/-- `φ_N^*` is additive. -/
instance linearPairPushforward_additive :
    (PresheafOfModules.pushforward.{w} (linearPairRingHom.{v, u} (A := A) N)).Additive :=
  additive_presheafPushforward _

/-- `φ_N^*` preserves finite limits. -/
instance linearPairPushforward_preservesFiniteLimits :
    PreservesFiniteLimits
      (PresheafOfModules.pushforward.{w} (linearPairRingHom.{v, u} (A := A) N)) :=
  preservesFiniteLimits_presheafPushforward _

/-- `φ_N^*` preserves finite colimits. -/
instance linearPairPushforward_preservesFiniteColimits :
    PreservesFiniteColimits
      (PresheafOfModules.pushforward.{w} (linearPairRingHom.{v, u} (A := A) N)) :=
  preservesFiniteColimits_presheafPushforward _

/-- `ψ_N^*` is additive. -/
instance symPairPushforward_additive :
    (PresheafOfModules.pushforward.{w} (symPairRingHom.{v, u} (A := A) N)).Additive :=
  additive_presheafPushforward _

/-- `ψ_N^*` preserves finite limits. -/
instance symPairPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{w} (symPairRingHom.{v, u} (A := A) N)) :=
  preservesFiniteLimits_presheafPushforward _

/-- `ψ_N^*` preserves finite colimits. -/
instance symPairPushforward_preservesFiniteColimits :
    PreservesFiniteColimits
      (PresheafOfModules.pushforward.{w} (symPairRingHom.{v, u} (A := A) N)) :=
  preservesFiniteColimits_presheafPushforward _

attribute [local instance] moduleValuedFunctor_enoughInjectives in
/-- **Extension groups along `φ_N^* ⊣ ψ_N^*`.** For a module-valued functor `F` on pairs and a
module-valued functor `G` on `A`-algebras, applying `φ_N^*` and then the counit gives a bijection
`Ext^n(F, (C, V) ↦ G(Sym_C(V ⊗_A N))) ≃ Ext^n(D ↦ F(D, Hom_A(N, D)), G)`. -/
theorem extMap_pairsPushforwardAdjunction_bijective
    [HasExt.{t} (PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)]
    [HasExt.{t'} (ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)]
    (F : PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
    (G : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (n : ℕ) :
    Function.Bijective
      (Stacks.ExtAdjunction.extMap
        (pairsPushforwardAdjunction.{max (u + 1) (v + 1) w, v, u} N) F G n) :=
  Stacks.ExtAdjunction.extMap_bijective _ F G n

end Ext

section ExtOn

variable {A : Type u} [CommRing A] {N : Type (max u v)} [AddCommGroup N] [Module A N]
  {Pr : ObjectProperty (CommAlgCat.{max u v} A)}
  {Qr : ObjectProperty (AlgebraModulePair.{max u v} A)} (h : PairsDomainClosed N Pr Qr)

open Stacks.AlgebraicGeometry.RestrictionExact CategoryTheory.Limits

/-- `φ_N^*` on the domains is additive. -/
instance linearPairPushforwardOn_additive :
    (PresheafOfModules.pushforward.{w} (linearPairRingHomOn h)).Additive :=
  additive_presheafPushforward _

/-- `φ_N^*` on the domains preserves finite limits. -/
instance linearPairPushforwardOn_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{w} (linearPairRingHomOn h)) :=
  preservesFiniteLimits_presheafPushforward _

/-- `φ_N^*` on the domains preserves finite colimits. -/
instance linearPairPushforwardOn_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafOfModules.pushforward.{w} (linearPairRingHomOn h)) :=
  preservesFiniteColimits_presheafPushforward _

/-- `ψ_N^*` on the domains is additive. -/
instance symPairPushforwardOn_additive :
    (PresheafOfModules.pushforward.{w} (symPairRingHomOn h)).Additive :=
  additive_presheafPushforward _

/-- `ψ_N^*` on the domains preserves finite limits. -/
instance symPairPushforwardOn_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{w} (symPairRingHomOn h)) :=
  preservesFiniteLimits_presheafPushforward _

/-- `ψ_N^*` on the domains preserves finite colimits. -/
instance symPairPushforwardOn_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafOfModules.pushforward.{w} (symPairRingHomOn h)) :=
  preservesFiniteColimits_presheafPushforward _

attribute [local instance] moduleValuedFunctor_enoughInjectives in
/-- **Extension groups along `φ_N^* ⊣ ψ_N^*` on the domains.** For a module-valued functor `F`
on the allowed pairs and a module-valued functor `G` on the allowed algebras, applying `φ_N^*`
and then the counit gives a bijection
`Ext^n(F, (C, V) ↦ G(Sym_C(V ⊗_A N))) ≃ Ext^n(D ↦ F(D, Hom_A(N, D)), G)`. -/
theorem extMap_pairsPushforwardAdjunctionOn_bijective
    [HasExt.{t} (PresheafOfModules.{max (u + 1) (v + 1) w} (pairRingDiagramOn Qr))]
    [HasExt.{t'} (PresheafOfModules.{max (u + 1) (v + 1) w} (algebraRingDiagramOn.{v} Pr.ι))]
    (F : PresheafOfModules.{max (u + 1) (v + 1) w} (pairRingDiagramOn Qr))
    (G : PresheafOfModules.{max (u + 1) (v + 1) w} (algebraRingDiagramOn.{v} Pr.ι)) (n : ℕ) :
    Function.Bijective
      (Stacks.ExtAdjunction.extMap
        (pairsPushforwardAdjunctionOn.{max (u + 1) (v + 1) w} h) F G n) :=
  Stacks.ExtAdjunction.extMap_bijective _ F G n

end ExtOn

end AdequateFunctor
