module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Descent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Prestack

/-!
# Morphisms of small étale sheaves glue, for any coefficient category

The canonical functor from sheaves on the small étale site of `S` to descent data for a covering,
in the pseudofunctor of small étale inverse images, is fully faithful. Unlike its essential
surjectivity, this needs no limits in the coefficient category: it is the prestack property of
sheaves on slice sites (Stacks 04TQ), moved along the same comparisons as
`AlgebraicGeometry.SmallEtaleGluing.isEquivalence_toDescentData`.

## Main results

* `AlgebraicGeometry.SmallEtaleGluing.fullyFaithful_toDescentData` — the full faithfulness.

## References

* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace CategoryTheory.Pseudofunctor

variable {C : Type*} [Category C] {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
  {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Full faithfulness of the canonical functor to descent data is invariant under a fibrewise
equivalence of pseudofunctors. -/
public def StrongTrans.fullyFaithfulToDescentData (τ : StrongTrans F G)
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsEquivalence)
    (h : (F.toDescentData f).FullyFaithful) : (G.toDescentData f).FullyFaithful :=
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.Full := have := hτ a; inferInstance
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.Faithful := have := hτ a; inferInstance
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.EssSurj := have := hτ a; inferInstance
  have := τ.isEquivalence_descentDataFunctor f
  have := hτ (.mk (op S))
  let e := (τ.app (.mk (op S))).toFunctor.asEquivalence
  ((e.fullyFaithfulInverse.comp
      (h.comp (τ.descentDataFunctor f).asEquivalence.fullyFaithfulFunctor)).ofIso
    (Functor.isoWhiskerLeft e.inverse (τ.toDescentDataCompDescentDataFunctorIso f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso (G.toDescentData f) ≪≫ Functor.leftUnitor _))

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

namespace SmallEtaleGluing

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (S : B.Scheme)

/-- **Morphisms of small étale sheaves glue (Stacks 04TQ), phrased with inverse images.** For a
family of objects `V k` of the small étale site of `S` covering its final object, the canonical
functor from sheaves on the small étale site of `S` to descent data for the structure morphisms of
the `V k`, in the pseudofunctor of small étale inverse images, is fully faithful. -/
public def fullyFaithful_toDescentData
    {ι : Type*} (V : ι → SmallEtale B S.1 S.property)
    (hV : Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property)) :
    ((pseudofunctor B A).toDescentData (fun k => (V k).obj.hom)).FullyFaithful := by
  let g := fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)
  have : ((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).IsPrestack
      (SmallEtale.topology B S.1 S.property) :=
    GrothendieckTopology.isPrestack_pseudofunctorOver _ A
  let h0 := ((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).fullyFaithfulToDescentData
    g hV
  let h1 := Pseudofunctor.StrongTrans.fullyFaithfulToDescentData g
    (((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).transportStrongTrans
      (fibre B A S) (fibreEquiv B A S))
    (Pseudofunctor.isEquivalence_transportStrongTrans_app _ _ _) h0
  let h2 := Pseudofunctor.StrongTrans.fullyFaithfulToDescentData g (strongTrans B A S)
    (isEquivalence_strongTrans_app B A S) h1
  let sq := fun i j => ChosenPullback.ofHasPullback (g i) (g j)
  have := Pseudofunctor.isEquivalence_restrictDescentData (pseudofunctor B A) (forget B S) sq
    (fun i j ↦ (sq i j).isPullback.map (forget B S))
    (fun _ _ _ ↦ ChosenPullback₃.ofHasPullbacks _ _ _)
    (fun i j k ↦ (ChosenPullback₃.ofHasPullbacks (sq i j) (sq j k) (sq i k)).isPullback₂.map
      (forget B S))
  have h3 : ((pseudofunctor B A).toDescentData (fun i => (forget B S).map (g i)) ⋙
      Pseudofunctor.restrictDescentData (pseudofunctor B A) (forget B S) g).FullyFaithful :=
    h2.ofIso (Pseudofunctor.toDescentDataCompRestrictDescentDataIso (pseudofunctor B A)
      (forget B S) g).symm
  exact h3.ofCompFaithful

end SmallEtaleGluing

end AlgebraicGeometry

end
