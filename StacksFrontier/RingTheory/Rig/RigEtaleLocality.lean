module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality

/-!
# Rig-étaleness is a local property of arrows of `WAdm^Noeth`

A continuous homomorphism of Noetherian adic topological rings is rig-étale (Stacks 0GCV) when
it is adic of topologically finite type — condition (6) of Stacks 0GBW — and a power of an ideal
of definition of its source annihilates the identity of the completed naive cotangent complex of
its target in the derived category of modules over that target.  Stacks 0AQL asserts that this
is a *local property* in the sense of Situation 0CBA, in the Noetherian form of Remark 0ANI:
rig-étaleness ascends along a completed étale localization diagram, descends along one whose
target-side horizontal map is faithfully flat, and is preserved by finite products of targets.

The two halves of the condition are separated here, exactly as in Stacks 0GCK, whose proof the
Stacks Project's proof of 0AQL reproduces verbatim.  `Rig.RigEtaleCondition` isolates the
annihilation half, and the locality of that half is taken as an input; the finite-type half is
proved, because it is the locality of Stacks 0GBW, and the passage between "some ideal of
definition" and "every ideal of definition" is Stacks 0GCU.

## Main definitions

* `Rig.RigEtaleCondition` — the annihilation half of rig-étaleness, as a property of a
  homomorphism of topological rings: for every ideal of definition of the source and every
  witness that the arrow is an adic finite-type algebra, the resulting algebra is rig-étale
  over that ideal in the sense of Stacks 0GAY.

## Main results

* `Rig.rigEtale_isLocalNoetherian` — **Stacks 0AQL**, granted the locality of
  `Rig.RigEtaleCondition`.

## Implementation notes

The three locality axioms are quantified over the subcategory of Noetherian adic rings, so each
corner of a localization diagram and each factor of a finite product comes with adicness and
Noetherianity.  `RingHom.IsRigEtaleArrow` quantifies over the linear-topology and Noetherian
instances of its source and target instead of demanding them, so in each axiom those instances
arrive as hypotheses of the goal and never have to be constructed — except for the product of a
finite family, whose adicness is `Rig.isAdic_pi`.

`Rig.IsRigEtaleOver` bundles the completeness and finite-type data of its target existentially,
whereas `Rig.adicFiniteTypeAlgebra` takes that data as an argument; the two descriptions of the
same object agree definitionally by proof irrelevance, and `Rig.isRigEtaleOver_of_isRigEtale`
records the resulting translation.

## References

* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
* [Stacks Project, Tag 0GCU](https://stacks.math.columbia.edu/tag/0GCU)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
-/

@[expose] public noncomputable section

open CategoryTheory Filter
open scoped Topology

namespace Rig

attribute [local instance] HasDerivedCategory.standard

universe u v

/-- The annihilation half of rig-étaleness (Stacks 0GCV), as a property of a homomorphism of
topological rings: whenever the source is linearly topologized and Noetherian and the arrow
exhibits its target as an adic algebra of finite type over an ideal of definition `I` of the
source, that algebra is rig-étale over `I` in the sense of Stacks 0GAY.  By Stacks 0GCU the
quantifier over `I` is immaterial for a continuous arrow of `WAdm^Noeth`. -/
public abbrev RigEtaleCondition {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) : Prop :=
  ∀ [IsLinearTopology A A] [IsLinearTopology B B] [IsNoetherianRing A] [IsNoetherianRing B]
    (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I),
    Rig.IsRigEtale (Rig.adicFiniteTypeAlgebra φ hft I hI)

/-- Rig-étaleness of the adic finite-type algebra cut out by an ideal of definition is
rig-étaleness over that ideal in the sense of `Rig.IsRigEtaleOver`: the completeness and
finite-type data the latter asks for are supplied by the finite-type condition of Stacks
0GBW. -/
public theorem isRigEtaleOver_of_isRigEtale {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (h : Rig.IsRigEtale (Rig.adicFiniteTypeAlgebra φ hft I hI)) :
    Rig.IsRigEtaleOver φ I :=
  ⟨(isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal φ hft I hI).1,
    (isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal φ hft I hI).2, h⟩

/-- For Noetherian adic rings, "adic of topologically finite type" implies the adic finite-type
algebra condition for every ideal of definition. -/
private theorem finiteTypeAdicAlgebraForEveryIdeal_of_adic_and_finiteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hA : TopologicalRing.IsAdic A) (hAN : IsNoetherianRing A)
    (hB : TopologicalRing.IsAdic B) (hBN : IsNoetherianRing B)
    (h : RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :
    Rig.FiniteTypeAdicAlgebraForEveryIdeal φ :=
  ((Rig.adicFiniteType_tfae φ hA hB (exists_idealOfDefinition_fg hA hAN)
    (exists_idealOfDefinition_fg hB hBN)).out 1 6).mp h

/-- For Noetherian adic rings, the adic finite-type algebra condition for every ideal of
definition implies "adic of topologically finite type". -/
private theorem adic_and_finiteType_of_finiteTypeAdicAlgebraForEveryIdeal {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hA : TopologicalRing.IsAdic A) (hAN : IsNoetherianRing A)
    (hB : TopologicalRing.IsAdic B) (hBN : IsNoetherianRing B)
    (h : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) :
    RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ :=
  ((Rig.adicFiniteType_tfae φ hA hB (exists_idealOfDefinition_fg hA hAN)
    (exists_idealOfDefinition_fg hB hBN)).out 6 1).mp h

/-- A rig-étale continuous homomorphism of adic rings satisfies `Rig.RigEtaleCondition`. -/
private theorem rigEtaleCondition_of_isRigEtale_of_adic {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (hA : TopologicalRing.IsAdic A)
    (hB : TopologicalRing.IsAdic B) (h : RingHom.IsRigEtale φ) : Rig.RigEtaleCondition φ := by
  intro _ _ _ _ _ J hJ
  exact (h.forall_idealOfDefinition hφ hA hB J hJ).2.2

/-- A special case of `Rig.rigEtale_propertyIsLocalNoetherian`: rig-étaleness is a local property
of arrows of `WAdm^Noeth`, granted that same locality for `Rig.RigEtaleCondition` (the hypothesis
`hcond`). The full, unconditional version is not available in this module: it is proved
downstream, in `StacksFrontier.RingTheory.Rig.RigEtaleIsLocal`, which imports this file. -/
public theorem rigEtale_isLocalNoetherian
    (hcond : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ)) :
    TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hP _ _ _ _
    let : IsNoetherianRing A := hA.2
    let : IsNoetherianRing B := hB.2
    have hPmap : Continuous D.map ∧ RingHom.IsRigEtale D.map := hP
    obtain ⟨-, hft, hex⟩ := hPmap
    have hone := adic_and_finiteType_of_finiteTypeAdicAlgebraForEveryIdeal D.map
      hB.1 hB.2 hA.1 hA.2 hft
    have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal.localizationPreserves
      D (exists_fg_isAdic hA.1 hA.2) (exists_fg_isAdic hB.1 hB.2)
      (exists_fg_isAdic hA'.1 hA'.2) (exists_fg_isAdic hB'.1 hB'.2) hone
    have hft' := finiteTypeAdicAlgebraForEveryIdeal_of_adic_and_finiteType D.completedMap
      hB'.1 hB'.2 hA'.1 hA'.2 hcomp
    have hPc := rigEtaleCondition_of_isRigEtale_of_adic D.map D.continuousMap hB.1 hA.1 ⟨hft, hex⟩
    obtain ⟨I', hI', -⟩ := hB'.1.1
    exact ⟨D.continuousCompletedMap, hft', I', hI',
      isRigEtaleOver_of_isRigEtale D.completedMap hft' I' hI'
        (hcond.localizationPreserves D hA hB hA' hB' hPc hft' I' hI')⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hP _ _ _ _
    let : IsNoetherianRing (TopologicalRing.CompletionOver D.toA') := hA'.2
    let : IsNoetherianRing (TopologicalRing.CompletionOver D.toB') := hB'.2
    have hPmap : Continuous D.completedMap ∧ RingHom.IsRigEtale D.completedMap := hP
    obtain ⟨-, hft', hex'⟩ := hPmap
    have hone' := adic_and_finiteType_of_finiteTypeAdicAlgebraForEveryIdeal D.completedMap
      hB'.1 hB'.2 hA'.1 hA'.2 hft'
    have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal.faithfullyFlatDescent
      D (exists_fg_isAdic hA.1 hA.2) (exists_fg_isAdic hB.1 hB.2)
      (exists_fg_isAdic hA'.1 hA'.2) (exists_fg_isAdic hB'.1 hB'.2) hFF hone'
    have hft := finiteTypeAdicAlgebraForEveryIdeal_of_adic_and_finiteType D.map
      hB.1 hB.2 hA.1 hA.2 hcomp
    have hPc := rigEtaleCondition_of_isRigEtale_of_adic D.completedMap D.continuousCompletedMap
      hB'.1 hA'.1 ⟨hft', hex'⟩
    obtain ⟨I, hI, -⟩ := hB.1.1
    exact ⟨D.continuousMap, hft, I, hI,
      isRigEtaleOver_of_isRigEtale D.map hft I hI
        (hcond.faithfullyFlatDescent D hA hB hA' hB' hFF hPc hft I hI)⟩
  · intro B _ _ _ _ hBweak hBcount ι _ A _ _ _ _ hAweak hAcount f hf hCB hCA hPi _ _ _ _
    let : ∀ i, IsNoetherianRing (A i) := fun i ↦ (hCA i).2
    have hPi' : ∀ i, Continuous (f i) ∧ RingHom.IsRigEtale (f i) := fun i ↦ hPi i
    have hprodadic : TopologicalRing.IsAdic (∀ i, A i) := isAdic_pi A fun i ↦ (hCA i).1
    have hone := fun i ↦ adic_and_finiteType_of_finiteTypeAdicAlgebraForEveryIdeal (f i)
      hCB.1 hCB.2 (hCA i).1 (hCA i).2 (hPi' i).2.1
    have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal.finiteProduct
      hBweak hBcount A hAweak hAcount f hf (exists_fg_isAdic hCB.1 hCB.2)
      (fun i ↦ exists_fg_isAdic (hCA i).1 (hCA i).2) hone
    have hft := finiteTypeAdicAlgebraForEveryIdeal_of_adic_and_finiteType (RingHom.pi f)
      hCB.1 hCB.2 hprodadic inferInstance hcomp
    have hPc : ∀ i, Rig.RigEtaleCondition (f i) := fun i ↦
      rigEtaleCondition_of_isRigEtale_of_adic (f i) (hf i) hCB.1 (hCA i).1 (hPi' i).2
    obtain ⟨I, hI, -⟩ := hCB.1.1
    exact ⟨continuous_pi hf, hft, I, hI,
      isRigEtaleOver_of_isRigEtale (RingHom.pi f) hft I hI
        (hcond.finiteProduct hBweak hBcount A hAweak hAcount f hf hCB hCA hPc hft I hI)⟩

end Rig

end
