module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproductFunctorial
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdicProduct

/-!
# The weak-ideal diagram of a finite product of weakly admissible rings

Let `A k` be a finite family of weakly admissible linearly topologized rings and let each `A k`
carry a diagram `D k` of affine schemes over `S` indexed by its weak ideals of definition whose
stages are the spectra of the quotients of `A k`, as in
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation`. This file assembles those into one
such diagram for the product ring `∏ A k`, indexed by the weak ideals of definition of `∏ A k`,
whose stages are the spectra of the quotients of `∏ A k`.

A weak ideal of definition `J` of `∏ A k` has weak ideals of definition of the factors as its
projections `J.map (Pi.evalRingHom A k)`, and the projection is monotone, so it is a functor
`weakIdealsPiProj` on the index categories. Composing it with `D k` puts all the members on the
common index `WeakIdeals (∏ A k)`, where the pointwise coproduct
`AlgebraicGeometry.BigAffineFppf.sigmaFunctor` turns them into a single diagram.

## Main definitions

* `AlgebraicGeometry.FormalSpace.quotPiEvalEquiv`: the quotient of a finite product of rings by
  an ideal, identified with the product of the quotients of the factors by the projections of
  that ideal.
* `AlgebraicGeometry.FormalSpace.weakIdealsPiProj`: the projection of the weak ideals of
  definition of a finite product of weakly admissible rings to those of a factor, as a functor
  of the index categories.
* `AlgebraicGeometry.FormalSpace.sigmaWeakIdealDiagram`: the pointwise coproduct of a finite
  family of weak-ideal diagrams, as a diagram indexed by the weak ideals of definition of the
  product ring.
* `AlgebraicGeometry.FormalSpace.sigmaWeakIdealQuotientIso`: its stages, identified with the
  spectra of the quotients of the product ring.

## Main results

* `AlgebraicGeometry.FormalSpace.pi_factor_comp_quotPiEvalEquiv`: the identification
  `quotPiEvalEquiv` carries the quotient map of a pair of nested ideals of the product to the
  product of the quotient maps of their projections.
* `AlgebraicGeometry.FormalSpace.sigmaWeakIdealQuotientIso_natural`: the transition morphisms of
  `sigmaWeakIdealDiagram` are induced by the canonical quotient homomorphisms of the product
  ring, provided those of each member are.

## Implementation notes

The family of rings is indexed by a type in the universe `u` of the schemes, because `∏ A k` is
a ring in `Type u` only then; the index type of a coproduct in the site may be larger, and
`AlgebraicGeometry.BigAffineFppf.sigmaObjIsoSpecPi` therefore takes a `u`-small model of it.
Here the coproduct is formed over the `u`-small index of the rings itself, so the model is the
identity equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The quotient of a finite product of rings by an ideal -/

section Quot

variable {K : Type*} [Finite K] (A : K → Type*) [∀ k, CommRing (A k)]

/-- **The quotient of a finite product of rings by an ideal is the product of the quotients of
the factors by the projections of that ideal.** -/
noncomputable def quotPiEvalEquiv (J : Ideal (∀ k, A k)) :
    ((∀ k, A k) ⧸ J) ≃+* ∀ k, A k ⧸ J.map (Pi.evalRingHom A k) :=
  (Ideal.quotEquivOfEq (Ideal.piOrderIso.symm_apply_apply J).symm).trans
    (TopologicalRing.piQuotEquiv fun k ↦ J.map (Pi.evalRingHom A k))

/-- The identification `AlgebraicGeometry.FormalSpace.quotPiEvalEquiv` sends the class of `a` to
the family of the classes of its components. -/
@[simp]
theorem quotPiEvalEquiv_mk (J : Ideal (∀ k, A k)) (a : ∀ k, A k) (k : K) :
    quotPiEvalEquiv A J (Ideal.Quotient.mk J a) k =
      Ideal.Quotient.mk (J.map (Pi.evalRingHom A k)) (a k) :=
  rfl

/-- The identification `AlgebraicGeometry.FormalSpace.quotPiEvalEquiv` carries the canonical
quotient homomorphism of a pair of nested ideals of a finite product of rings to the product of
the canonical quotient homomorphisms of their projections. -/
theorem pi_factor_comp_quotPiEvalEquiv {J J' : Ideal (∀ k, A k)} (h : J' ≤ J)
    (h' : ∀ k, J'.map (Pi.evalRingHom A k) ≤ J.map (Pi.evalRingHom A k)) :
    (RingHom.pi fun k ↦ (Ideal.Quotient.factor (h' k)).comp
          (Pi.evalRingHom (fun k ↦ A k ⧸ J'.map (Pi.evalRingHom A k)) k)).comp
        (quotPiEvalEquiv A J' : _ →+* _) =
      (quotPiEvalEquiv A J : _ →+* _).comp (Ideal.Quotient.factor h) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ funext fun k ↦ ?_)
  simp [RingHom.pi_apply, Ideal.Quotient.factor_mk]

end Quot

/-! ### The weak-ideal diagram of a finite product -/

section Sigma

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {K : Type u} [Finite K] (A : K → Type u) [∀ k, CommRing (A k)]
  [∀ k, TopologicalSpace (A k)] [∀ k, IsTopologicalRing (A k)]
  [∀ k, IsLinearTopology (A k) (A k)]
  (hA : ∀ k, TopologicalRing.IsWeaklyAdmissible (A k))

/-- Projecting a weak ideal of definition of a finite product of weakly admissible rings to a
factor is monotone. -/
theorem monotone_weakIdealOfDefinitionPiProj (k : K) :
    Monotone fun J : TopologicalRing.WeakIdealOfDefinitionIndex (∀ k, A k) ↦
      (⟨J.1.map (Pi.evalRingHom A k),
        TopologicalRing.isWeakIdealOfDefinition_map_evalRingHom A hA J.2 k⟩ :
          TopologicalRing.WeakIdealOfDefinitionIndex (A k)) :=
  fun _ _ hJ ↦ Ideal.map_mono hJ

/-- **The projection to a factor of the weak ideals of definition of a finite product of weakly
admissible linearly topologized rings**, as a functor of the index categories of
`AlgebraicGeometry.FormalSpace.WeakIdeals`, sending a weak ideal of definition `J` to its image
`J.map (Pi.evalRingHom A k)`. -/
def weakIdealsPiProj (k : K) : WeakIdeals (∀ k, A k) ⥤ WeakIdeals (A k) :=
  (monotone_weakIdealOfDefinitionPiProj A hA k).dual.functor

/-- The projection of a weak ideal of definition `J` to the factor `A k` is the image of `J` under
the `k`-th evaluation. -/
@[simp]
theorem weakIdealsPiProj_obj_coe (k : K) (J : WeakIdeals (∀ k, A k)) :
    ((weakIdealsPiProj A hA k).obj J).1 = J.1.map (Pi.evalRingHom A k) :=
  rfl

/-- **The weak-ideal diagram of a finite product of weakly admissible rings**: the pointwise
coproduct of a finite family of diagrams of affine schemes over `S`, the member indexed by `A k`
reindexed along `AlgebraicGeometry.FormalSpace.weakIdealsPiProj` so that all of them are indexed
by the weak ideals of definition of the product ring. -/
noncomputable def sigmaWeakIdealDiagram (D : ∀ k, WeakIdeals (A k) ⥤ BigAffineFppf B S hS) :
    WeakIdeals (∀ k, A k) ⥤ BigAffineFppf B S hS :=
  BigAffineFppf.sigmaFunctor B S hS fun k ↦ weakIdealsPiProj A hA k ⋙ D k

/-- The stage of `AlgebraicGeometry.FormalSpace.sigmaWeakIdealDiagram` at `J` is the coproduct of
the stages of the members at the projections of `J`. -/
@[simp]
theorem sigmaWeakIdealDiagram_obj (D : ∀ k, WeakIdeals (A k) ⥤ BigAffineFppf B S hS)
    (J : WeakIdeals (∀ k, A k)) :
    (sigmaWeakIdealDiagram B S hS A hA D).obj J =
      BigAffineFppf.sigmaObj B S hS fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J) :=
  rfl

/-- The transition morphism of `AlgebraicGeometry.FormalSpace.sigmaWeakIdealDiagram` along `f` is
the coproduct of the transition morphisms of the members along the projections of `f`. -/
@[simp]
theorem sigmaWeakIdealDiagram_map (D : ∀ k, WeakIdeals (A k) ⥤ BigAffineFppf B S hS)
    {J J' : WeakIdeals (∀ k, A k)} (f : J ⟶ J') :
    (sigmaWeakIdealDiagram B S hS A hA D).map f =
      BigAffineFppf.sigmaMap B S hS fun k ↦ (D k).map ((weakIdealsPiProj A hA k).map f) :=
  rfl

variable (D : ∀ k, WeakIdeals (A k) ⥤ BigAffineFppf B S hS)
  (q : ∀ (k : K) (J : WeakIdeals (A k)),
    (BigAffineFppf.toScheme B S hS).obj ((D k).obj J) ≅ Spec (.of (A k ⧸ J.1)))

/-- **The stages of the weak-ideal diagram of a finite product are the spectra of the quotients of
the product ring.** It is the identification `AlgebraicGeometry.BigAffineFppf.sigmaObjIsoSpecPi` of
the underlying scheme of a finite coproduct with the spectrum of the product of the rings
presenting the summands, followed by the spectrum of
`AlgebraicGeometry.FormalSpace.quotPiEvalEquiv`. -/
noncomputable def sigmaWeakIdealQuotientIso (J : WeakIdeals (∀ k, A k)) :
    (BigAffineFppf.toScheme B S hS).obj ((sigmaWeakIdealDiagram B S hS A hA D).obj J) ≅
      Spec (.of ((∀ k, A k) ⧸ J.1)) :=
  BigAffineFppf.sigmaObjIsoSpecPi B S hS (Equiv.refl K)
      (fun k ↦ .of (A k ⧸ J.1.map (Pi.evalRingHom A k)))
      (fun k ↦ q k ((weakIdealsPiProj A hA k).obj J)) ≪≫
    Scheme.Spec.mapIso (quotPiEvalEquiv A J.1).toCommRingCatIso.op

/-- The forward morphism of `AlgebraicGeometry.FormalSpace.sigmaWeakIdealQuotientIso` is that of
`AlgebraicGeometry.BigAffineFppf.sigmaObjIsoSpecPi` followed by the spectrum of
`AlgebraicGeometry.FormalSpace.quotPiEvalEquiv`. -/
@[simp]
theorem sigmaWeakIdealQuotientIso_hom (J : WeakIdeals (∀ k, A k)) :
    (sigmaWeakIdealQuotientIso B S hS A hA D q J).hom =
      (BigAffineFppf.sigmaObjIsoSpecPi B S hS (Equiv.refl K)
          (fun k ↦ .of (A k ⧸ J.1.map (Pi.evalRingHom A k)))
          (fun k ↦ q k ((weakIdealsPiProj A hA k).obj J))).hom ≫
        Spec.map (CommRingCat.ofHom (quotPiEvalEquiv A J.1)) :=
  rfl

/-- **The transition morphisms of the weak-ideal diagram of a finite product are induced by the
canonical quotient homomorphisms of the product ring**, provided those of the members are. -/
theorem sigmaWeakIdealQuotientIso_natural
    (hq : ∀ (k : K) ⦃J J' : WeakIdeals (A k)⦄ (f : J ⟶ J'),
      (BigAffineFppf.toScheme B S hS).map ((D k).map f) ≫ (q k J').hom =
        (q k J).hom ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (show J'.1 ≤ J.1 from leOfHom f))))
    ⦃J J' : WeakIdeals (∀ k, A k)⦄ (f : J ⟶ J') :
    (BigAffineFppf.toScheme B S hS).map ((sigmaWeakIdealDiagram B S hS A hA D).map f) ≫
        (sigmaWeakIdealQuotientIso B S hS A hA D q J').hom =
      (sigmaWeakIdealQuotientIso B S hS A hA D q J).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (show J'.1 ≤ J.1 from leOfHom f))) := by
  have hle : ∀ k, J'.1.map (Pi.evalRingHom A k) ≤ J.1.map (Pi.evalRingHom A k) := fun _ ↦
    Ideal.map_mono (leOfHom f)
  have hnat := BigAffineFppf.sigmaObjIsoSpecPi_hom_naturality B S hS (Equiv.refl K)
    (A := fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J))
    (A' := fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J'))
    (fun k ↦ .of (A k ⧸ J.1.map (Pi.evalRingHom A k)))
    (fun k ↦ .of (A k ⧸ J'.1.map (Pi.evalRingHom A k)))
    (fun k ↦ q k ((weakIdealsPiProj A hA k).obj J))
    (fun k ↦ q k ((weakIdealsPiProj A hA k).obj J'))
    (fun k ↦ (D k).map ((weakIdealsPiProj A hA k).map f))
    (fun k ↦ CommRingCat.ofHom (Ideal.Quotient.factor (hle k)))
    (fun k ↦ hq k ((weakIdealsPiProj A hA k).map f))
  rw [sigmaWeakIdealDiagram_map, sigmaWeakIdealQuotientIso_hom, sigmaWeakIdealQuotientIso_hom]
  refine (Category.assoc' _ _ _).trans
    (((eq_whisker hnat _).trans ((Category.assoc _ _ _).trans ?_)).trans
      (Category.assoc' _ _ _))
  refine whisker_eq _ ?_
  refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_comp _ _))
  exact (CommRingCat.ofHom_comp _ _).symm.trans
    ((congrArg CommRingCat.ofHom (pi_factor_comp_quotPiEvalEquiv A (leOfHom f) hle)).trans
      (CommRingCat.ofHom_comp _ _))

end Sigma

end AlgebraicGeometry.FormalSpace

end
