module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.Topology.Irreducible
public import StacksCore.Tactic.StacksAttribute

/-!
# Galois action on geometric irreducible components

An automorphism of an algebra over a base ring acts on the corresponding base change of a
scheme. The induced homeomorphism of the underlying space sends irreducible components to
irreducible components, giving the canonical action on geometric irreducible components. For an
extension of ground fields, an embedding of chosen separable closures induces both a restriction
map on Galois groups and a bijection on geometric irreducible components, and the two canonical
Galois actions are compatible with this bijection.

## Main definitions

* `AlgebraicGeometry.SchemeOver.baseChange` is the base change of a scheme over `Spec R`.
* `AlgebraicGeometry.specMapAlgAut` is the automorphism of `Spec S` attached to an algebra
  automorphism of `S`.
* `AlgebraicGeometry.galoisActionOnBaseChange` is the action on the base-changed scheme.
* `AlgebraicGeometry.galoisActionOnGeometricIrreducibleComponents` is the action of the opposite
  of the group of algebra automorphisms on the irreducible components after base change.
* `AlgebraicGeometry.baseChangeComparison` is the canonical map between the two base changes
  induced by an embedding of extension fields.

## Main results

* `AlgebraicGeometry.galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe`: the action sends
  a component to its image under the corresponding automorphism of the base-changed scheme.
* `AlgebraicGeometry.galoisActionOnGeometricIrreducibleComponents_equivariant`: the bijection on
  geometric irreducible components is equivariant for restriction of Galois automorphisms.

## Implementation notes

The action is constructed first on the scheme-theoretic pullback, is transported to its
underlying topological space by `CategoryTheory.Functor.mapAction`, and is then restricted to
Mathlib's subtype `irreducibleComponents`. It is stated for an arbitrary extension of
commutative rings, since the construction itself does not use the field or separable-closure
hypotheses.

Chosen embeddings of separable closures are represented by compatible algebra structures. The
bijection on components is supplied together with the assertion that it is induced by the
canonical projection; writing it explicitly keeps the commutative diagram, rather than merely
its underlying cardinality, visible in the statement.

## References

* [Stacks Project, Tag 038A](https://stacks.math.columbia.edu/tag/038A)
* [Stacks Project, Tag 038J](https://stacks.math.columbia.edu/tag/038J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

namespace AlgebraicGeometry

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The base change of a scheme over `Spec R` to `Spec S`. -/
public noncomputable abbrev SchemeOver.baseChange
    (X : Over (Spec (.of R))) : Scheme :=
  ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj X).left

/-- The automorphism of `Spec S` associated to an `R`-algebra automorphism of `S`. -/
public noncomputable def specMapAlgAut (σ : S ≃ₐ[R] S) :
    Spec (.of S) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)

/-- The identity automorphism induces the identity of `Spec S`. -/
@[simp]
public theorem specMapAlgAut_one : specMapAlgAut R S 1 = 𝟙 (Spec (.of S)) := by
  unfold specMapAlgAut
  rw [show (1 : S ≃ₐ[R] S).toRingEquiv.toRingHom = RingHom.id S by ext; rfl]
  exact Spec.map_id _

/-- Taking spectra turns composition of automorphisms into composition in the other order. -/
public theorem specMapAlgAut_mul (σ τ : S ≃ₐ[R] S) :
    specMapAlgAut R S (σ * τ) = specMapAlgAut R S σ ≫ specMapAlgAut R S τ := by
  unfold specMapAlgAut; rw [← Spec.map_comp]; congr 1

/-- The automorphism of `Spec S` attached to an `R`-algebra automorphism lies over `Spec R`. -/
@[reassoc (attr := simp)]
public theorem specMapAlgAut_comp_structureMap (σ : S ≃ₐ[R] S) :
    specMapAlgAut R S σ ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  unfold specMapAlgAut; rw [← Spec.map_comp]; congr 1
  ext r; exact σ.commutes r

/-- The action of the opposite algebra-automorphism group on a scheme after base change. -/
@[implicit_reducible, sga "7 XIII 1.1.1"]
public noncomputable def galoisActionOnBaseChange
    (X : Over (Spec (.of R))) :
    Action Scheme (MulOpposite (S ≃ₐ[R] S)) where
  V := SchemeOver.baseChange R S X
  ρ :=
    { toFun := fun σ =>
        pullback.map X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (𝟙 X.left) (specMapAlgAut R S σ.unop)
          (𝟙 (Spec (.of R))) (by simp)
          (by simp)
      map_one' := by
        simp
      map_mul' := fun σ τ => by
        symm
        simpa [specMapAlgAut_mul] using
          (pullback.map_comp (f := X.hom)
            (g := Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (f' := X.hom) (g' := Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (f'' := X.hom) (g'' := Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (𝟙 X.left) (𝟙 X.left) (specMapAlgAut R S τ.unop)
            (specMapAlgAut R S σ.unop) (𝟙 (Spec (.of R))) (𝟙 (Spec (.of R)))
            (by simp) (by simp) (by simp) (by simp)) }

add_to_stacks 038A "For a Galois extension `kbar/k` the group `kbar ≃ₐ[k] kbar` is `Gal(kbar/k)`,
  and `galoisActionOnBaseChange` is the canonical action of its opposite group on `X_kbar`,
  induced by the automorphisms `Spec σ` of `Spec kbar` through the defining fibre product.
  The opposite group appears because `Spec σ ≫ Spec τ = Spec (τ ∘ σ)`."
  AlgebraicGeometry.galoisActionOnBaseChange

/-- An action by homeomorphisms restricts canonically to the irreducible components. -/
@[implicit_reducible]
public noncomputable def irreducibleComponentsAction {G : Type u} [Group G]
    (X : Action TopCat G) : Action (Type u) G := by
  let : MulAction G X.V := Action.instMulAction X
  let : MulAction G ↥(irreducibleComponents X.V) :=
    { smul g Z :=
        ⟨(fun x => g • x) '' Z.1, by
          let e := TopCat.homeoOfIso (X.ρAut g)
          exact image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
            e.isOpenMap
            (fun x => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
            e.surjective Z.2⟩
      one_smul Z := by
        apply Subtype.ext
        change (fun x : X.V => (1 : G) • x) '' Z.1 = Z.1
        simp
      mul_smul g h Z := by
        apply Subtype.ext
        change (fun x : X.V => (g * h) • x) '' Z.1 =
          (fun x : X.V => g • x) '' ((fun x : X.V => h • x) '' Z.1)
        rw [Set.image_image]; simp only [mul_smul] }
  exact Action.ofMulAction G ↥(irreducibleComponents X.V)

/-- The canonical action of the opposite Galois group on the irreducible components of a scheme
after base change. A component is sent to its image under the corresponding automorphism of the
base-changed scheme. -/
@[stacks 038J "galois_action_on_geometric_irreducible_components", implicit_reducible]
public noncomputable def galoisActionOnGeometricIrreducibleComponents
    (X : Over (Spec (.of R))) :
    Action (Type u) (MulOpposite (S ≃ₐ[R] S)) :=
  irreducibleComponentsAction
    ((Scheme.forgetToTop.mapAction (MulOpposite (S ≃ₐ[R] S))).obj
      (galoisActionOnBaseChange R S X))

/-- The Galois action sends an irreducible component to its pointwise image under the
corresponding automorphism of the base-changed scheme. -/
@[simp]
public theorem galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe
    (X : Over (Spec (.of R))) (σ : MulOpposite (S ≃ₐ[R] S))
    (Z : (galoisActionOnGeometricIrreducibleComponents R S X).V) :
    (ConcreteCategory.hom
      ((galoisActionOnGeometricIrreducibleComponents R S X).ρ σ) Z).1 =
      (fun x => Scheme.forget.map ((galoisActionOnBaseChange R S X).ρ σ) x) '' Z.1 :=
  rfl

/-- The canonical projection from the base change along `R → T` to the base change along
`R → S`, for a compatible tower `R → S → T`. -/
public noncomputable def baseChangeComparison
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) :
    pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⟶
      pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  pullback.lift
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (by
      rw [pullback.condition, Category.assoc, ← Spec.map_comp]
      congr 2
      ext x
      exact IsScalarTower.algebraMap_apply R S T x)

/-- The comparison map between two geometric base changes is equivariant for restriction of
Galois automorphisms. -/
private theorem baseChangeComparison_naturality
    (k k' ksep ksep' : Type u)
    [Field k] [Field k'] [Field ksep] [Field ksep']
    [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [Algebra k ksep']
    [Algebra ksep ksep'] [IsScalarTower k k' ksep'] [IsScalarTower k ksep ksep']
    [IsSepClosure k ksep] [IsSepClosure k' ksep']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (σ : ksep' ≃ₐ[k'] ksep') :
    (galoisActionOnBaseChange k ksep' (Over.mk f)).ρ
        (MulOpposite.op (AlgEquiv.restrictScalars k σ)) ≫
      baseChangeComparison k ksep ksep' X f =
    baseChangeComparison k ksep ksep' X f ≫
      (galoisActionOnBaseChange k ksep (Over.mk f)).ρ
        (MulOpposite.op ((AlgEquiv.restrictNormalHom ksep)
          (AlgEquiv.restrictScalars k σ))) := by
  have hspec :
      specMapAlgAut k ksep' (AlgEquiv.restrictScalars k σ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ksep ksep')) =
        Spec.map (CommRingCat.ofHom (algebraMap ksep ksep')) ≫
          specMapAlgAut k ksep ((AlgEquiv.restrictNormalHom ksep)
            (AlgEquiv.restrictScalars k σ)) := by
    unfold specMapAlgAut
    rw [← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext x
    exact (AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars k σ) ksep x).symm
  dsimp [galoisActionOnBaseChange, SchemeOver.baseChange]
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [Category.assoc, Category.comp_id, baseChangeComparison, pullback.map,
      CategoryTheory.Limits.pullback.lift_fst]
  · simp only [Category.assoc, Category.comp_id, baseChangeComparison, pullback.map,
      CategoryTheory.Limits.pullback.lift_snd,
      CategoryTheory.Limits.pullback.lift_snd_assoc]
    rw [hspec]

/-- The bijection `e` on geometric irreducible components induced by an embedding of separable
closures, given as a bijection sending each component to its image under
`AlgebraicGeometry.baseChangeComparison`, intertwines the Galois action over the extended field
with the action over the original field via restriction of automorphisms. -/
public theorem galoisActionOnGeometricIrreducibleComponents_equivariant
    (k k' ksep ksep' : Type u)
    [Field k] [Field k'] [Field ksep] [Field ksep']
    [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [Algebra k ksep']
    [Algebra ksep ksep'] [IsScalarTower k k' ksep'] [IsScalarTower k ksep ksep']
    [IsSepClosure k ksep] [IsSepClosure k' ksep']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (e : irreducibleComponents
        (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap k ksep')))) ≃
      irreducibleComponents
        (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))))
    (he : ∀ Z, (e Z : Set _) =
      (baseChangeComparison k ksep ksep' X f).base '' (Z : Set _))
    (σ : MulOpposite (ksep' ≃ₐ[k'] ksep'))
    (Z : (galoisActionOnGeometricIrreducibleComponents k ksep' (Over.mk f)).V) :
    e (ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k ksep' (Over.mk f)).ρ
          (MulOpposite.op (AlgEquiv.restrictScalars k σ.unop))) Z) =
      ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).ρ
            (MulOpposite.op
              ((AlgEquiv.restrictNormalHom ksep)
                (AlgEquiv.restrictScalars k σ.unop))))
        (e Z) := by
  have hrightAction :=
    galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe k ksep (Over.mk f)
      (MulOpposite.op ((AlgEquiv.restrictNormalHom ksep)
        (AlgEquiv.restrictScalars k σ.unop))) (e Z)
  apply Subtype.ext
  have hleft := he (ConcreteCategory.hom
    ((galoisActionOnGeometricIrreducibleComponents k ksep' (Over.mk f)).ρ
      (MulOpposite.op (AlgEquiv.restrictScalars k σ.unop))) Z)
  rw [hleft, galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe, hrightAction]
  show (baseChangeComparison k ksep ksep' X f).base ''
      ((fun x => Scheme.forget.map
        ((galoisActionOnBaseChange k ksep' (Over.mk f)).ρ
          (MulOpposite.op (AlgEquiv.restrictScalars k σ.unop))) x) '' Z.1) = _
  rw [he Z]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(baseChangeComparison k ksep ksep' X f).base y, ⟨y, hy, rfl⟩, ?_⟩
    simpa [TopCat.coe_comp] using (congrArg (fun q => q.base y)
      (baseChangeComparison_naturality k k' ksep ksep' X f σ.unop)).symm
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Scheme.forget.map
      ((galoisActionOnBaseChange k ksep' (Over.mk f)).ρ
        (MulOpposite.op (AlgEquiv.restrictScalars k σ.unop))) z, ⟨z, hz, rfl⟩, ?_⟩
    simpa [TopCat.coe_comp] using congrArg (fun q => q.base z)
      (baseChangeComparison_naturality k k' ksep ksep' X f σ.unop)

end AlgebraicGeometry
