module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteProduct

/-!
# The presenting ring of a finite coproduct of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `Z i`, indexed by a finite type, be
affine formal algebraic spaces over `S` each presented, in the sense of condition (1) of Stacks
0AIC, by a weakly admissible topological ring `A i`. Then the coproduct `∐ Z` is presented by
the product ring `∀ i, A i`.

The weak ideals of definition of a finite product ring are exactly the products of weak ideals
of definition of the factors, by `TopologicalRing.weakIdealOfDefinitionIndexPiOrderIso`, so the
index of the presentation of `∀ i, A i` is the product of the indices of the presentations of
the factors; that product is the index of
`AlgebraicGeometry.FormalSpace.sigmaStage`, whose colimit is `∐ Z` by
`AlgebraicGeometry.FormalSpace.sigmaColimitIso`. The stage of that diagram at a product ideal is
the coproduct of the stages of the factors, and its underlying scheme is therefore the coproduct
of the spectra of the quotients `A i ⧸ J i`, which is the spectrum of their product by Mathlib's
`AlgebraicGeometry.sigmaSpec` — that is, of `(∀ i, A i) ⧸ Ideal.pi J` by
`TopologicalRing.piQuotEquiv`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.piWeakIdealsOrderIso`: the weak ideals of definition of a
  finite product ring, as the index of the product diagram.
* `AlgebraicGeometry.FormalSpace.piQuotRingIso`: the quotient of a finite product ring by a weak
  ideal of definition, as the product of the quotients of the factors.
* `AlgebraicGeometry.FormalSpace.piStageSchemeIso`: the underlying scheme of a stage of the
  product diagram, as the spectrum of a quotient of the product ring.
* `AlgebraicGeometry.FormalSpace.stageColimitIsoOfOrderIso`: a presentation of a sheaf by a
  directed diagram of affine schemes, reindexed along an order isomorphism.

## Main results

* `AlgebraicGeometry.FormalSpace.weakIdealColimitPresentation_pi_sigma`: **the product of the
  presenting rings presents the coproduct.**
* `AlgebraicGeometry.FormalSpace.isPresentingRing_pi_sigma`: the same, in the form of
  `AlgebraicGeometry.FormalSpace.IsPresentingRing`.

## Implementation notes

The index of the coproduct in Definition 0AIM lives in `Type (u + 1)` while a presenting ring
lives in `Type u`, so the product ring is formed over a `Type u` index `κ` and the coproduct is
taken over `ULift.{u + 1} κ`. A caller with an index in `Type (u + 1)` reindexes the coproduct
along an equivalence, which is harmless because all five types of Stacks 0AIJ and 0AID are
invariant under isomorphism of the sheaf.

The indices of the presentations of the factors are likewise lifted, so the diagram presenting
the factor at `i` is precomposed with the order isomorphism
`AlgebraicGeometry.FormalSpace.uliftOrderIso`; that functor is an equivalence, so it changes no
colimit.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe w v u

/-! ### Order isomorphisms -/

section OrderIsos

/-- The universe lift of a preorder, as an order isomorphism onto it. -/
def uliftOrderIso (α : Type w) [Preorder α] : ULift.{v} α ≃o α where
  toEquiv := Equiv.ulift
  map_rel_iff' := Iff.rfl

/-- The order dual of a product is the product of the order duals: both orders are the
pointwise reversed order. -/
def piDualOrderIso {κ : Type u} (X : κ → Type u) [∀ c, Preorder (X c)] :
    (∀ c, X c)ᵒᵈ ≃o ∀ c, (X c)ᵒᵈ where
  toEquiv := Equiv.refl _
  map_rel_iff' := Iff.rfl

/-- A product over a `Type u` index, as a product with lifted factors over its universe
lift. -/
def piULiftOrderIso {κ : Type u} (X : κ → Type u) [∀ c, Preorder (X c)] :
    (∀ c, X c) ≃o ∀ i : ULift.{v} κ, ULift.{v} (X i.down) where
  toFun g i := ULift.up (g i.down)
  invFun f c := (f (ULift.up c)).down
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h c ↦ h (ULift.up c), fun h i ↦ h i.down⟩

/-- `AlgebraicGeometry.FormalSpace.StageIndex` is the product of its factors, as an order
isomorphism. -/
def stageIndexOrderIso {I : Type (u + 1)} (Idx : I → Type (u + 1)) [∀ i, Preorder (Idx i)] :
    (∀ i, Idx i) ≃o StageIndex Idx where
  toFun g := ⟨g⟩
  invFun lam := lam.coord
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The universe lift of a directed order is directed. -/
theorem isDirectedOrder_ulift (α : Type w) [Preorder α] [IsDirectedOrder α] :
    IsDirectedOrder (ULift.{v} α) :=
  ⟨fun a b ↦
    let ⟨c, hc₁, hc₂⟩ := exists_ge_ge a.down b.down
    ⟨ULift.up c, hc₁, hc₂⟩⟩

end OrderIsos

/-! ### The spectrum of a finite product of rings -/

section SigmaSpec

variable {κ : Type u} [Finite κ] (R : κ → CommRingCat.{u})

/-- **The spectrum of a finite product of rings is the coproduct of the spectra**, with the
coproduct taken over the universe lift of the index. This is Mathlib's
`AlgebraicGeometry.sigmaSpec` reindexed, the index of a coproduct of sheaves in Definition 0AIM
living one universe above the rings. -/
def uliftSigmaSpec : (∐ fun i : ULift.{u + 1} κ ↦ Spec (R i.down)) ≅ Spec (.of (∀ c, R c)) :=
  Sigma.whiskerEquiv (Equiv.ulift (α := κ)) (f := fun i : ULift.{u + 1} κ ↦ Spec (R i.down))
      (g := fun c : κ ↦ Spec (R c)) (fun _ ↦ Iso.refl _) ≪≫
    asIso (sigmaSpec R)

/-- The coprojection at `i` followed by `uliftSigmaSpec R` is the morphism of spectra induced by
the projection of `∀ c, R c` onto the factor `R i.down`. -/
@[reassoc]
theorem ι_uliftSigmaSpec (i : ULift.{u + 1} κ) :
    Sigma.ι (fun i : ULift.{u + 1} κ ↦ Spec (R i.down)) i ≫ (uliftSigmaSpec R).hom =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun c ↦ (R c : Type u)) i.down)) := by
  have h : Sigma.ι (fun i : ULift.{u + 1} κ ↦ Spec (R i.down)) i ≫
      (Sigma.whiskerEquiv (Equiv.ulift (α := κ))
        (f := fun i : ULift.{u + 1} κ ↦ Spec (R i.down))
        (g := fun c : κ ↦ Spec (R c)) (fun _ ↦ Iso.refl _)).hom =
      Sigma.ι (fun c : κ ↦ Spec (R c)) i.down :=
    (Sigma.ι_comp_map' _ _ i).trans (Category.id_comp _)
  change Sigma.ι (fun i : ULift.{u + 1} κ ↦ Spec (R i.down)) i ≫
    ((Sigma.whiskerEquiv (Equiv.ulift (α := κ))
      (f := fun i : ULift.{u + 1} κ ↦ Spec (R i.down))
      (g := fun c : κ ↦ Spec (R c)) (fun _ ↦ Iso.refl _)).hom ≫ sigmaSpec R) = _
  rw [← Category.assoc, h, ι_sigmaSpec]

end SigmaSpec

/-! ### Lifting the index of a presenting diagram -/

section UliftStage

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presentation of a sheaf by a diagram of affine schemes stays one after the index is
reindexed along an order isomorphism — in particular after it is lifted to the universe of the
index of Definition 0AIM: an order isomorphism is an equivalence of categories, and so changes
no colimit. -/
def stageColimitIsoOfOrderIso {α : Type w} [Preorder α] {β : Type (u + 1)} [Preorder β]
    (ε : β ≃o α) (D : α ⥤ BigAffineFppf B S hS)
    [HasColimit (D ⋙ affineStageSheafFunctor B S hS)]
    [HasColimit ((ε.equivalence.functor ⋙ D) ⋙ affineStageSheafFunctor B S hS)]
    (X : FppfSheaf B S hS) (e : X ≅ colimit (D ⋙ affineStageSheafFunctor B S hS)) :
    X ≅ colimit ((ε.equivalence.functor ⋙ D) ⋙ affineStageSheafFunctor B S hS) :=
  e ≪≫ (Functor.Final.colimitIso ε.equivalence.functor
      (D ⋙ affineStageSheafFunctor B S hS)).symm ≪≫
    (HasColimit.isoOfNatIso (Functor.associator ε.equivalence.functor D
      (affineStageSheafFunctor B S hS))).symm

end UliftStage

/-! ### The index and the diagram of the product presentation -/

section Index

variable {κ : Type u} (A : κ → Type u) [∀ c, CommRing (A c)] [∀ c, TopologicalSpace (A c)]

/-- The index of the presentation of the factor at `i`, lifted into the universe of the index of
Definition 0AIM. -/
abbrev piCoproductIdx (i : ULift.{u + 1} κ) : Type (u + 1) :=
  ULift.{u + 1} (WeakIdeals (A i.down))

/-- **The index of the presentation of a finite product ring.** The weak ideals of definition of
`∀ c, A c` are exactly the products of weak ideals of definition of the factors, so, ordered by
reverse inclusion, they are the index of the product diagram
`AlgebraicGeometry.FormalSpace.sigmaStage` of the presentations of the factors. -/
def piWeakIdealsOrderIso [Finite κ] :
    WeakIdeals (∀ c, A c) ≃o StageIndex (piCoproductIdx A) :=
  (TopologicalRing.weakIdealOfDefinitionIndexPiOrderIso (A := A)).dual.trans
    (((piDualOrderIso fun c ↦ TopologicalRing.WeakIdealOfDefinitionIndex (A c)).trans
      (piULiftOrderIso fun c ↦ WeakIdeals (A c))).trans
        (stageIndexOrderIso (piCoproductIdx A)))

/-- The coordinate at `c` of a weak ideal of definition of the product ring: its image under
the projection, which is a weak ideal of definition of the factor. -/
abbrev piCoordWeakIdeal [Finite κ] (J : WeakIdeals (∀ c, A c)) (c : κ) : WeakIdeals (A c) :=
  ⟨Ideal.map (Pi.evalRingHom A c) J.1,
    TopologicalRing.isWeakIdealOfDefinition_map_evalRingHom' J.2 c⟩

/-- The coordinates of the index of the product presentation are the coordinates of the weak
ideal of definition. -/
theorem coord_piWeakIdealsOrderIso [Finite κ] (J : WeakIdeals (∀ c, A c))
    (i : ULift.{u + 1} κ) :
    ((piWeakIdealsOrderIso A J).coord i).down = piCoordWeakIdeal A J i.down :=
  rfl

/-- The quotient of a finite product ring by a weak ideal of definition is the product of the
quotients of the factors by its coordinates. -/
def piQuotRingIso [Finite κ] (J : WeakIdeals (∀ c, A c)) :
    ((∀ c, A c) ⧸ J.1) ≃+*
      ∀ c, A c ⧸ (piCoordWeakIdeal A J c).1 :=
  (Ideal.quotEquivOfEq (show Ideal.pi (fun c ↦ J.1.map (Pi.evalRingHom A c)) = J.1 from
    Ideal.piOrderIso.symm_apply_apply J.1).symm).trans
    (TopologicalRing.piQuotEquiv _)

/-- The isomorphism `piQuotRingIso A J` sends the class of `x` to the family of classes of its
coordinates. -/
@[simp]
theorem piQuotRingIso_mk [Finite κ] (J : WeakIdeals (∀ c, A c)) (x : ∀ c, A c) (c : κ) :
    piQuotRingIso A J (Ideal.Quotient.mk _ x) c = Ideal.Quotient.mk _ (x c) := by
  simp [piQuotRingIso, piCoordWeakIdeal]

/-- The projection of the quotient of the product ring by a weak ideal of definition onto the
quotient of a factor commutes with the transition maps of both quotient systems: both
composites send the class of an element to the class of its coordinate. -/
theorem factor_comp_eval_comp_piQuotRingIso [Finite κ]
    {J K : WeakIdeals (∀ c, A c)} (h : K.1 ≤ J.1)
    (c : κ) :
    (Ideal.Quotient.factor (Ideal.map_mono h :
          (piCoordWeakIdeal A K c).1 ≤ (piCoordWeakIdeal A J c).1)).comp
        ((Pi.evalRingHom (fun d ↦ A d ⧸ (piCoordWeakIdeal A K d).1) c).comp
          (piQuotRingIso A K).toRingHom) =
      ((Pi.evalRingHom (fun d ↦ A d ⧸ (piCoordWeakIdeal A J d).1) c).comp
          (piQuotRingIso A J).toRingHom).comp (Ideal.Quotient.factor h) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)
  simp [Ideal.Quotient.factor_mk, piCoordWeakIdeal]

end Index

/-! ### The presentation -/

section Presentation

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {κ : Type u} (A : κ → Type u) [∀ c, CommRing (A c)] [∀ c, TopologicalSpace (A c)]
  (Z : ULift.{u + 1} κ → FppfSheaf B S hS)
  (P : ∀ i : ULift.{u + 1} κ, WeakIdealColimitPresentation B S hS (A i.down) (Z i))

/-- The diagram presenting the factor at `i`, reindexed by the lifted index. -/
def piCoproductDiagram (i : ULift.{u + 1} κ) :
    piCoproductIdx A i ⥤ BigAffineFppf B S hS :=
  (uliftOrderIso (WeakIdeals (A i.down))).equivalence.functor ⋙ (P i).diagram

/-- The quotient of the factor at `c` by the coordinate at `c` of a weak ideal of definition of
the product ring. -/
abbrev piQuotRing [Finite κ] (J : WeakIdeals (∀ c, A c)) (c : κ) : CommRingCat.{u} :=
  CommRingCat.of (A c ⧸ (piCoordWeakIdeal A J c).1)

/-- The stage at `i` of the coproduct of the stages of the factors over a weak ideal of
definition of the product ring. -/
abbrev piStageObj [Finite κ] (J : WeakIdeals (∀ c, A c)) (i : ULift.{u + 1} κ) :
    BigAffineFppf B S hS :=
  (P i).diagram.obj (piCoordWeakIdeal A J i.down)

/-- **The stage of the product presentation is the spectrum of a quotient of the product
ring.** The stage is the finite coproduct of the stages of the factors; its underlying scheme is
the coproduct of the spectra of the quotients `A c ⧸ J c`, which is the spectrum of the product
of those quotients, and that product is the quotient of `∀ c, A c` by `J`. -/
def piStageSchemeIso [Finite κ] (J : WeakIdeals (∀ c, A c)) :
    (BigAffineFppf.toScheme B S hS).obj (∐ fun i ↦ piStageObj B S hS A Z P J i) ≅
      Spec (.of ((∀ c, A c) ⧸ J.1)) :=
  (toSchemeSigmaIso B S hS fun i ↦ piStageObj B S hS A Z P J i).symm ≪≫
    Sigma.mapIso (g := fun i : ULift.{u + 1} κ ↦ Spec (piQuotRing A J i.down))
      (fun i ↦ (P i).quotientIso (piCoordWeakIdeal A J i.down)) ≪≫
    uliftSigmaSpec (piQuotRing A J) ≪≫
    Scheme.Spec.mapIso (piQuotRingIso A J).toCommRingCatIso.op

/-- `sigmaι_toSchemeSigmaIso_hom`, with a morphism composed on the right. -/
private theorem sigmaι_comp_toSchemeSigmaIso_hom_comp {ι : Type (u + 1)} [Finite ι]
    (W : ι → BigAffineFppf B S hS) (i : ι) {T : Scheme.{u}}
    (g : (BigAffineFppf.toScheme B S hS).obj (∐ W) ⟶ T) :
    Sigma.ι (fun i ↦ (BigAffineFppf.toScheme B S hS).obj (W i)) i ≫
        (toSchemeSigmaIso B S hS W).hom ≫ g =
      (BigAffineFppf.toScheme B S hS).map (Sigma.ι W i) ≫ g := by
  rw [← Category.assoc, sigmaι_toSchemeSigmaIso_hom]

/-- **The component of `AlgebraicGeometry.FormalSpace.piStageSchemeIso` at a factor.** On the
stage of the factor at `i` it is the identification of that stage with `Spec (A i ⧸ J i)`
followed by the spectrum of the projection of `(∀ c, A c) ⧸ J` onto that quotient. -/
theorem toScheme_map_sigmaι_piStageSchemeIso_hom [Finite κ] (J : WeakIdeals (∀ c, A c))
    (i : ULift.{u + 1} κ) :
    (BigAffineFppf.toScheme B S hS).map (Sigma.ι (fun i ↦ piStageObj B S hS A Z P J i) i) ≫
        (piStageSchemeIso B S hS A Z P J).hom =
      ((P i).quotientIso (piCoordWeakIdeal A J i.down)).hom ≫
        Spec.map (CommRingCat.ofHom
          ((Pi.evalRingHom (fun c ↦ (piQuotRing A J c : Type u)) i.down).comp
            (piQuotRingIso A J).toRingHom)) := by
  have hι : (BigAffineFppf.toScheme B S hS).map
        (Sigma.ι (fun i ↦ piStageObj B S hS A Z P J i) i) ≫
      (toSchemeSigmaIso B S hS fun i ↦ piStageObj B S hS A Z P J i).inv =
      Sigma.ι (fun i ↦ (BigAffineFppf.toScheme B S hS).obj
        (piStageObj B S hS A Z P J i)) i := by
    exact (Iso.comp_inv_eq _).2
      (sigmaι_toSchemeSigmaIso_hom B S hS (fun i ↦ piStageObj B S hS A Z P J i) i).symm
  change (BigAffineFppf.toScheme B S hS).map (Sigma.ι (fun i ↦ piStageObj B S hS A Z P J i) i) ≫
    ((toSchemeSigmaIso B S hS fun i ↦ piStageObj B S hS A Z P J i).inv ≫
      ((Sigma.mapIso (g := fun i : ULift.{u + 1} κ ↦ Spec (piQuotRing A J i.down))
          (fun i ↦ (P i).quotientIso (piCoordWeakIdeal A J i.down))).hom ≫
        ((uliftSigmaSpec (piQuotRing A J)).hom ≫
          Spec.map (CommRingCat.ofHom (piQuotRingIso A J).toRingHom)))) = _
  rw [← Category.assoc, hι, Sigma.ι_mapIso_hom_assoc, ι_uliftSigmaSpec_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

/-- **The identification of the stages of the product presentation with the spectra of the
quotients of the product ring is natural.** On each factor it is the naturality of the
identification carried by the presentation of that factor, followed by the compatibility of the
projections of the quotients of the product ring with the transition maps. -/
theorem piStageSchemeIso_natural [Finite κ] {J K : WeakIdeals (∀ c, A c)} (f : J ⟶ K) :
    (BigAffineFppf.toScheme B S hS).map
        (Limits.Sigma.map fun i ↦ (P i).diagram.map
          (homOfLE (show piCoordWeakIdeal A J i.down ≤ piCoordWeakIdeal A K i.down from
            Ideal.map_mono (leOfHom f)))) ≫
        (piStageSchemeIso B S hS A Z P K).hom =
      (piStageSchemeIso B S hS A Z P J).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom f))) := by
  refine (cancel_epi (toSchemeSigmaIso B S hS fun i ↦ piStageObj B S hS A Z P J i).hom).mp ?_
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [sigmaι_comp_toSchemeSigmaIso_hom_comp, sigmaι_comp_toSchemeSigmaIso_hom_comp,
    ← Category.assoc, ← Functor.map_comp, Sigma.ι_map, Functor.map_comp,
    Category.assoc, toScheme_map_sigmaι_piStageSchemeIso_hom, ← Category.assoc,
    (P i).quotientIso_natural, ← Category.assoc,
    toScheme_map_sigmaι_piStageSchemeIso_hom, Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom
    (factor_comp_eval_comp_piQuotRingIso A (show K.1 ≤ J.1 from leOfHom f) i.down)

/-- The diagram of the product presentation: the product diagram
`AlgebraicGeometry.FormalSpace.sigmaStage` of the diagrams presenting the factors, reindexed by
the weak ideals of definition of the product ring. -/
def piPresentationDiagram [Finite κ] : WeakIdeals (∀ c, A c) ⥤ BigAffineFppf B S hS :=
  (piWeakIdealsOrderIso A).equivalence.functor ⋙
    sigmaStage B S hS (piCoproductIdx A) (piCoproductDiagram B S hS A Z P)

/-- The factor at `i` is the colimit of its presenting diagram reindexed by the lifted index:
the reindexing is an equivalence of categories, so it changes no colimit. -/
def piFactorColimitIso (i : ULift.{u + 1} κ) :
    Z i ≅ colimit (piCoproductDiagram B S hS A Z P i ⋙ affineStageSheafFunctor B S hS) :=
  stageColimitIsoOfOrderIso B S hS (uliftOrderIso (WeakIdeals (A i.down))) (P i).diagram
    (Z i) (P i).colimitIso

/-- The coproduct of the factors is the colimit of the diagram of the product presentation, by
the interchange of a finite coproduct with the colimits presenting its summands and the
reindexing by the weak ideals of definition of the product ring. -/
def piPresentationColimitIso [Finite κ]
    [∀ i : ULift.{u + 1} κ, Nonempty (piCoproductIdx A i)]
    [∀ i : ULift.{u + 1} κ, IsDirectedOrder (piCoproductIdx A i)] :
    (∐ Z) ≅ colimit (piPresentationDiagram B S hS A Z P ⋙ affineStageSheafFunctor B S hS) :=
  sigmaColimitIso B S hS (piCoproductIdx A) (piCoproductDiagram B S hS A Z P) Z
      (piFactorColimitIso B S hS A Z P) ≪≫
    (Functor.Final.colimitIso (piWeakIdealsOrderIso A).equivalence.functor
      (sigmaStage B S hS (piCoproductIdx A) (piCoproductDiagram B S hS A Z P) ⋙
        affineStageSheafFunctor B S hS)).symm ≪≫
    (HasColimit.isoOfNatIso (Functor.associator
      (piWeakIdealsOrderIso A).equivalence.functor
      (sigmaStage B S hS (piCoproductIdx A) (piCoproductDiagram B S hS A Z P))
      (affineStageSheafFunctor B S hS))).symm

/-- **The product of the presenting rings presents the coproduct.** The three fields are
`AlgebraicGeometry.FormalSpace.piPresentationDiagram`,
`AlgebraicGeometry.FormalSpace.piStageSchemeIso` with its naturality, and
`AlgebraicGeometry.FormalSpace.piPresentationColimitIso`. -/
def weakIdealColimitPresentationPi [Finite κ]
    [∀ i : ULift.{u + 1} κ, Nonempty (piCoproductIdx A i)]
    [∀ i : ULift.{u + 1} κ, IsDirectedOrder (piCoproductIdx A i)] :
    WeakIdealColimitPresentation B S hS (∀ c, A c) (∐ Z) where
  diagram := piPresentationDiagram B S hS A Z P
  quotientIso J := piStageSchemeIso B S hS A Z P J
  quotientIso_natural _ _ f := piStageSchemeIso_natural B S hS A Z P f
  colimitIso := piPresentationColimitIso B S hS A Z P

end Presentation

/-! ### The presenting ring of a coproduct -/

section IsPresentingRing

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {κ : Type u} [Finite κ] (A : κ → Type u) [∀ c, CommRing (A c)] [∀ c, TopologicalSpace (A c)]
  [∀ c, IsTopologicalRing (A c)] [∀ c, IsLinearTopology (A c) (A c)]
  (Z : ULift.{u + 1} κ → FppfSheaf B S hS)

/-- **The product of the presenting rings of a finite family of affine formal algebraic spaces
presents their coproduct.** Both halves of condition (1) of Stacks 0AIC are inherited: the
product of weakly admissible rings is weakly admissible, and the product diagram of the
presentations is a presentation of the coproduct. -/
theorem isPresentingRing_pi_sigma
    (h : ∀ i : ULift.{u + 1} κ, IsPresentingRing B S hS (A i.down) (Z i)) :
    letI : IsLinearTopology (∀ c, A c) (∀ c, A c) := TopologicalRing.pi_isLinearTopology
    IsPresentingRing B S hS (∀ c, A c) (∐ Z) := by
  let : IsLinearTopology (∀ c, A c) (∀ c, A c) := TopologicalRing.pi_isLinearTopology
  refine ⟨TopologicalRing.isWeaklyAdmissible_pi' fun c ↦ (h (ULift.up c)).1, ?_⟩
  have : ∀ i : ULift.{u + 1} κ, Nonempty (piCoproductIdx A i) := fun i ↦
    ⟨ULift.up (TopologicalRing.nonempty_weakIdealOfDefinitionIndex (h i).1.1).some⟩
  have : ∀ i : ULift.{u + 1} κ, IsDirectedOrder (piCoproductIdx A i) := fun i ↦
    have := TopologicalRing.isDirected_weakIdealOfDefinitionIndex (A i.down)
    isDirectedOrder_ulift (WeakIdeals (A i.down))
  exact ⟨weakIdealColimitPresentationPi B S hS A Z fun i ↦ (h i).2.some⟩

end IsPresentingRing



end AlgebraicGeometry.FormalSpace

end
