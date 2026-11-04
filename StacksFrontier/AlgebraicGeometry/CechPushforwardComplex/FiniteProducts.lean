module

public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The complex of sections commutes with a functor preserving only finite products

`Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIso` identifies the
termwise image under `G : A ⥤ B` of the complex of sections `s(P(E))` of a simplicial
semi-representable object `E` with the complex of sections of `P ⋙ G`, for an additive `G`
preserving *all* products indexed by types in the universe `w` of the summands of `E`. This file
proves the same thing for a `G` preserving only the products indexed by *finite* types, provided
`E` is finite in every simplicial degree.

That is the generality tensoring with a module has: `N ⊗ -` preserves finite products and no
others. A hypercovering which is finite in every degree, such as the one
`Stacks.AlgebraicGeometry.UniversalPushforward.exists_finite_affine_hypercovering` produces for a
quasi-compact quasi-separated scheme, is exactly what makes the comparison an isomorphism again.

## Main definitions

* `Stacks.CechPushforward.cosimplicialObjectFunctorCompWhiskeringHom`: the comparison of
  `Stacks.CechPushforward.cosimplicialObjectFunctorCompWhiskeringIso` as a natural
  transformation, which needs no product-preservation hypothesis at all.
* `Stacks.CechPushforward.cosimplicialObjectFunctorCompWhiskeringIsoOfFinite`: that
  transformation as an isomorphism, for a degreewise finite `E`.
* `Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIsoOfFinite`: **the
  comparison of complexes for a degreewise finite `E` and a `G` preserving finite products.**

## Main results

* `Stacks.CechPushforward.preservesLimitsOfShape_discrete_of_preservesFiniteLimits`: a functor
  preserving finite limits preserves products indexed by a finite type in any universe.
* `Stacks.CechPushforward.finite_I_obj_op`: a simplicial object of formal coproducts which is
  finite in every degree indexed by a natural number is finite in every degree.
* `Stacks.CechPushforward.isIso_cosimplicialObjectFunctorCompWhiskeringHom`: the comparison of
  cosimplicial objects is an isomorphism under those hypotheses.
* `Stacks.CechPushforward.cochainComplexFunctor_map_f` and
  `Stacks.CechPushforward.isIso_cochainComplexFunctor_map`: the degree-`n` component of the map
  of complexes of sections induced by a morphism of coefficient presheaves is the product of its
  components, so the induced map is an isomorphism as soon as those components are.

## Implementation notes

The comparison is a natural transformation before any hypothesis on `G`: its components are the
product comparison maps `CategoryTheory.Limits.piComparison`, which exist whenever the two
products do, and `Stacks.CechPushforward.evalOpCompHom` and
`Stacks.CechPushforward.evalOpCompWhiskeringRightHom` are already stated in that generality. So
nothing has to be rebuilt; only the step from a transformation to an isomorphism is redone, and
it is `CategoryTheory.NatIso.isIso_of_isIso_app` applied twice over, down to
`CategoryTheory.Limits.piComparison` at one summand type.

The degreewise finiteness hypothesis is stated for the degrees `⦋n⦌` with `n : ℕ`, which is the
form a hypercovering carries it in, and transported to an arbitrary object of `SimplexCategory`
along `SimplexCategory.mk_len`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.FormalCoproduct Opposite
open Simplicial

universe w v v' v'' u u' u''

namespace Stacks.CechPushforward

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B]

section FiniteProducts

variable [HasProducts.{w} A] [HasProducts.{w} B] (G : A ⥤ B)
  (E : SimplicialObject (FormalCoproduct.{w} C))

/-- **The cosimplicial object attached to a simplicial object of formal coproducts commutes with
an arbitrary functor, up to a natural transformation.**  Its components are the product
comparison maps, which need no preservation hypothesis to exist. -/
public noncomputable def cosimplicialObjectFunctorCompWhiskeringHom :
    cosimplicialObjectFunctor.{w} E ⋙ (CosimplicialObject.whiskering A B).obj G ⟶
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ cosimplicialObjectFunctor.{w} E where
  app P := Functor.whiskerLeft E.rightOp (evalOpCompHom.{w} G P)
  naturality _ _ α := by
    refine NatTrans.ext (funext fun n ↦ ?_)
    exact congrFun (congrArg NatTrans.app
      ((evalOpCompWhiskeringRightHom.{w} G).naturality α)) (E.rightOp.obj n)

/-- The components of `cosimplicialObjectFunctorCompWhiskeringHom` are the product comparison
maps of `G` at the summand types of `E`. -/
public theorem cosimplicialObjectFunctorCompWhiskeringHom_app_app (P : Cᵒᵖ ⥤ A)
    (n : SimplexCategory) :
    ((cosimplicialObjectFunctorCompWhiskeringHom.{w} G E).app P).app n =
      piComparison G (fun i : (E.obj (op n)).I ↦ P.obj (op ((E.obj (op n)).obj i))) :=
  rfl

/-- **A functor preserving finite limits preserves products indexed by a finite type**, in an
arbitrary universe: the index type is enumerated and the preservation transported along the
resulting equivalence of discrete categories.  `CategoryTheory.Limits.PreservesFiniteLimits`
itself quantifies over small categories only, so this is not a definitional unfolding. -/
@[sga "4 I 2.4.2" "necessity"]
public theorem preservesLimitsOfShape_discrete_of_preservesFiniteLimits
    {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D) [PreservesFiniteLimits G]
    (J : Type*) [Finite J] : PreservesLimitsOfShape (Discrete J) G := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have h : PreservesLimitsOfShape (Discrete (Fin n)) G := inferInstance
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence e).symm G

/-- **A simplicial object of formal coproducts finite in every degree `⦋n⦌` is finite in every
degree.**  Every object of `SimplexCategory` is `⦋n⦌` for `n` its length. -/
public theorem finite_I_obj_op (hE : ∀ n : ℕ, Finite (E.obj (op ⦋n⦌)).I)
    (n : SimplexCategory) : Finite (E.obj (op n)).I := by
  have h := hE n.len
  rwa [SimplexCategory.mk_len n] at h

/-- **The comparison of cosimplicial objects is an isomorphism** when `E` is finite in every
degree and `G` preserves products indexed by finite types. -/
public theorem isIso_cosimplicialObjectFunctorCompWhiskeringHom
    (hE : ∀ n : ℕ, Finite (E.obj (op ⦋n⦌)).I)
    (hG : ∀ (J : Type w) (_ : Finite J), PreservesLimitsOfShape (Discrete J) G) :
    IsIso (cosimplicialObjectFunctorCompWhiskeringHom.{w} G E) := by
  have happ : ∀ (P : Cᵒᵖ ⥤ A) (n : SimplexCategory),
      IsIso (((cosimplicialObjectFunctorCompWhiskeringHom.{w} G E).app P).app n) := by
    intro P n
    have hfin : Finite (E.obj (op n)).I := finite_I_obj_op.{w} E hE n
    have hpres : PreservesLimitsOfShape (Discrete (E.obj (op n)).I) G :=
      hG (E.obj (op n)).I hfin
    have h : IsIso (piComparison G
        (fun i : (E.obj (op n)).I ↦ P.obj (op ((E.obj (op n)).obj i)))) := inferInstance
    rw [cosimplicialObjectFunctorCompWhiskeringHom_app_app.{w} G E P n]
    exact h
  have : ∀ P : Cᵒᵖ ⥤ A,
      IsIso ((cosimplicialObjectFunctorCompWhiskeringHom.{w} G E).app P) := fun P ↦
    have := happ P
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- The comparison of cosimplicial objects as an isomorphism, under the hypotheses of
`isIso_cosimplicialObjectFunctorCompWhiskeringHom`. -/
public noncomputable def cosimplicialObjectFunctorCompWhiskeringIsoOfFinite
    (hE : ∀ n : ℕ, Finite (E.obj (op ⦋n⦌)).I)
    (hG : ∀ (J : Type w) (_ : Finite J), PreservesLimitsOfShape (Discrete J) G) :
    cosimplicialObjectFunctor.{w} E ⋙ (CosimplicialObject.whiskering A B).obj G ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ cosimplicialObjectFunctor.{w} E :=
  haveI := isIso_cosimplicialObjectFunctorCompWhiskeringHom.{w} G E hE hG
  asIso (cosimplicialObjectFunctorCompWhiskeringHom.{w} G E)

end FiniteProducts

section CochainComplex

variable [Preadditive A] [Preadditive B] [HasProducts.{w} A] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] (E : SimplicialObject (FormalCoproduct.{w} C))

/-- **The complex of sections of a degreewise finite simplicial formal coproduct commutes with an
additive functor preserving finite products.**  Applying `G` termwise to `s(P(E))` gives
`s((P ⋙ G)(E))`, naturally in the presheaf `P : Cᵒᵖ ⥤ A`.

This is `Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIso` with the
hypothesis on `G` weakened from all `w`-indexed products to the finite ones, at the cost of
degreewise finiteness of `E`. -/
public noncomputable def cochainComplexFunctorCompMapHomologicalComplexIsoOfFinite
    (hE : ∀ n : ℕ, Finite (E.obj (op ⦋n⦌)).I)
    (hG : ∀ (J : Type w) (_ : Finite J), PreservesLimitsOfShape (Discrete J) G) :
    cochainComplexFunctor.{w} E ⋙ G.mapHomologicalComplex _ ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ cochainComplexFunctor.{w} E :=
  Functor.isoWhiskerLeft (cosimplicialObjectFunctor.{w} E)
      (alternatingCofaceMapComplexCompMapHomologicalComplexIso G) ≪≫
    Functor.isoWhiskerRight (cosimplicialObjectFunctorCompWhiskeringIsoOfFinite.{w} G E hE hG)
      (AlgebraicTopology.alternatingCofaceMapComplex B)

/-- **The degree-`n` component of the map of complexes of sections induced by a morphism of
coefficient presheaves** is the product, over the summands of the `n`-th level of `E`, of its
components. -/
public theorem cochainComplexFunctor_map_f {P Q : Cᵒᵖ ⥤ A} (θ : P ⟶ Q) (n : ℕ) :
    ((cochainComplexFunctor.{w} E).map θ).f n =
      Limits.Pi.map (fun i : (E.obj (op ⦋n⦌)).I ↦ θ.app (op ((E.obj (op ⦋n⦌)).obj i))) :=
  rfl

/-- **A morphism of coefficient presheaves which is an isomorphism at every summand of `E`
induces an isomorphism of the complexes of sections.**  The hypothesis is imposed only at the
objects `E` is built from, which is what makes the statement usable for a comparison that is an
isomorphism over the affine opens of a hypercovering and nowhere else. -/
public theorem isIso_cochainComplexFunctor_map {P Q : Cᵒᵖ ⥤ A} (θ : P ⟶ Q)
    (hθ : ∀ (n : ℕ) (i : (E.obj (op ⦋n⦌)).I),
      IsIso (θ.app (op ((E.obj (op ⦋n⦌)).obj i)))) :
    IsIso ((cochainComplexFunctor.{w} E).map θ) := by
  have : ∀ n : ℕ, IsIso (((cochainComplexFunctor.{w} E).map θ).f n) := by
    intro n
    have := hθ n
    have h : IsIso (Limits.Pi.map
        (fun i : (E.obj (op ⦋n⦌)).I ↦ θ.app (op ((E.obj (op ⦋n⦌)).obj i)))) := inferInstance
    rw [cochainComplexFunctor_map_f.{w} E θ n]
    exact h
  exact HomologicalComplex.Hom.isIso_of_components _

end CochainComplex

end Stacks.CechPushforward

end
