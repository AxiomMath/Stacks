module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealProductColimit
public import StacksFrontier.RingTheory.Ideal.Pi
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality
public import StacksFrontier.RingTheory.Rig.RigSmoothStability
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdicProduct

/-!
# The types of a finite disjoint union of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. The proof of **Stacks 0AKX** uses that a
finite disjoint union of affine formal algebraic spaces having one of the properties of its list
— countably indexed, countably indexed and classical, weakly adic, adic\* and Noetherian — again
has that property ("small detail omitted on finite disjoint unions of affine formal algebraic
spaces"). Countable indexing is `AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma`. This
file supplies the four other properties.

Each of the four is a condition on a presenting ring, so the step needs a presenting ring of a
finite coproduct. That ring is the product of presenting rings of the summands: the coproduct of
the sheaves is the formal spectrum of the product ring by
`AlgebraicGeometry.FormalSpace.sigmaWeakIdealColimitPresentation`. What remains is to carry each
ring-theoretic condition across a finite product.

## Main results

* `TopologicalRing.isIdealOfDefinition_pi_ideal`: a product of ideals of definition of the
  factors, over a finite index type, is an ideal of definition of the product.
* `AlgebraicGeometry.FormalSpace.isPresentingRing_sigma_of_finite`: a finite coproduct of fppf
  sheaves presented by weakly admissible topological rings is McQuillan and is presented by the
  product of those rings.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_sigma`,
  `AlgebraicGeometry.FormalSpace.isWeaklyAdic_sigma`,
  `AlgebraicGeometry.FormalSpace.isAdicStar_sigma` and
  `AlgebraicGeometry.FormalSpace.isNoetherian_sigma`: the four properties pass to a finite
  disjoint union.

## Implementation notes

A presentation of an affine formal algebraic space is indexed by a type one universe above the
schemes, so the coproducts here are over an index in `Type (u + 1)`, whereas a product of rings
in `Type u` stays in `Type u` only over an index in `Type u`. A finite index type is `u`-small,
so the coproduct is identified with the coproduct over `Shrink.{u} I` by
`CategoryTheory.Limits.Sigma.whiskerEquiv`, the product ring is formed over that copy, and the
presentation is carried back along the identification.

None of these statements carries a `@[stacks]` registration: the Stacks project records the step
as a detail omitted inside the proof of Stacks 0AKX.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped Topology

namespace TopologicalRing

/-- **A product of ideals of definition of the factors, over a finite index type, is an ideal of
definition of the product.** It is open by `TopologicalRing.isOpen_idealPi`, and a rectangular
neighbourhood of zero of the product is caught by a single exponent because each factor's
neighbourhood is: the `i`-th component of an element of `(Ideal.pi I) ^ n` lies in `I i ^ n`. -/
theorem isIdealOfDefinition_pi_ideal {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]
    (I : ∀ i, Ideal (A i)) (hI : ∀ i, IsIdealOfDefinition (I i)) :
    IsIdealOfDefinition (Ideal.pi I : Ideal (∀ i, A i)) := by
  classical
  cases nonempty_fintype ι
  refine ⟨isOpen_idealPi A I fun i ↦ (hI i).1, fun U hU ↦ ?_⟩
  rw [nhds_pi] at hU
  obtain ⟨T, -, V, hV, hsub⟩ := Filter.mem_pi.mp hU
  choose m hm using fun i ↦ (hI i).2 (V i) (hV i)
  refine ⟨Finset.univ.sup m, fun x hx ↦ hsub fun i _ ↦ ?_⟩
  have hxi : x i ∈ ((Ideal.pi I) ^ Finset.univ.sup m).map (Pi.evalRingHom A i) :=
    Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow, Ideal.map_evalRingHom_pi] at hxi
  exact hm i (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) hxi)

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite coproduct of fppf sheaves each presented by a weakly admissible topological ring
is McQuillan, and the product of those rings presents it.** The product is formed over the
`u`-small copy `Shrink.{u} I` of the finite index type, exhibited in the conclusion as a type `K`
with a bijection `g : K → I`; the coproduct over `I` is identified with the coproduct over `K`
and the presentation of `AlgebraicGeometry.FormalSpace.sigmaWeakIdealColimitPresentation` is
carried back along that identification. The set-theoretic condition of Stacks 0AIS for the
coproduct is `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_sigma`, and the
McQuillan condition follows from the presentation by Stacks 0AIC. -/
theorem isPresentingRing_sigma_of_finite {I : Type (u + 1)} [Finite I] (A : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]
    [∀ i, IsLinearTopology (A i) (A i)] (Z : I → FppfSheaf B S hS)
    (hZ : ∀ i, SatisfiesSetTheoreticCondition B S hS (Z i))
    (hP : ∀ i, IsPresentingRing B S hS (A i) (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    HasSomeSurjectivePresentation B S hS (∐ Z) ∧
      ∃ (K : Type u) (_ : Finite K) (g : K → I), Function.Bijective g ∧
        letI : IsLinearTopology (∀ k, A (g k)) (∀ k, A (g k)) :=
          TopologicalRing.pi_isLinearTopology
        IsPresentingRing B S hS (∀ k, A (g k)) (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  change HasSomeSurjectivePresentation B S hS (∐ Z) ∧ _
  let : Small.{u} I := Countable.toSmall.{u} I
  have hfinK : Finite (Shrink.{u} I) := Finite.of_equiv _ (equivShrink.{u} I)
  set g : Shrink.{u} I → I := fun k ↦ (equivShrink.{u} I).symm k with hg
  let : IsLinearTopology (∀ k, A (g k)) (∀ k, A (g k)) :=
    TopologicalRing.pi_isLinearTopology
  have hwa : TopologicalRing.IsWeaklyAdmissible (∀ k, A (g k)) :=
    TopologicalRing.isWeaklyAdmissible_pi _ fun k ↦ (hP (g k)).1
  have hiso : (∐ Z) ≅ ∐ fun k ↦ Z (g k) :=
    Sigma.whiskerEquiv (equivShrink.{u} I) fun i ↦ eqToIso (by simp [hg])
  let P : WeakIdealColimitPresentation B S hS (∀ k, A (g k)) (∐ Z) :=
    (sigmaWeakIdealColimitPresentation B S hS (fun k ↦ A (g k)) (fun k ↦ (hP (g k)).1)
      (fun k ↦ Z (g k)) fun k ↦ (hP (g k)).2.some).ofIso hiso
  exact ⟨(hasAllSurjectivePresentations_of_weakIdealColimitPresentation B S hS
      (∀ k, A (g k)) hwa (satisfiesSetTheoreticCondition_sigma B S hS Z hZ)
      P).hasSomeSurjectivePresentation,
    Shrink.{u} I, hfinK, g, (equivShrink.{u} I).symm.bijective, hwa, ⟨P⟩⟩

/-- **A coproduct of finitely many countably indexed and classical affine formal algebraic spaces
is countably indexed and classical.** Countable indexing is
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma`; the presenting ring of the coproduct is
the product of presenting rings of the summands, and a finite product of admissible topological
rings is admissible. -/
theorem isCountablyIndexedAndClassical_sigma {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) (hZaff : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i))
    (hP : ∀ i, IsCountablyIndexed B S hS (Z i) ∧ IsClassical B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsCountablyIndexed B S hS (∐ Z) ∧ IsClassical B S hS (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨isCountablyIndexed_sigma B S hS Z fun i ↦ (hP i).1, ?_⟩
  choose A hCR hTS hTR hLT hApres hAadm using fun i ↦ (hP i).2.2
  let := hCR
  let := hTS
  let := hTR
  let := hLT
  obtain ⟨hsome, K, hK, g, -, hpres⟩ :=
    isPresentingRing_sigma_of_finite B S hS A Z (fun i ↦ (hZaff i).1) hApres
  exact ⟨hsome, (∀ k, A (g k)), inferInstance, inferInstance, inferInstance,
    TopologicalRing.pi_isLinearTopology, hpres,
    TopologicalRing.isAdmissible_pi _ fun k ↦ hAadm (g k)⟩

/-- **A coproduct of finitely many weakly adic affine formal algebraic spaces is weakly adic.**
The presenting ring of the coproduct is the product of presenting rings of the summands, and a
finite product of weakly adic linearly topologized rings is weakly adic. -/
theorem isWeaklyAdic_sigma {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) (hZaff : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i))
    (hP : ∀ i, IsWeaklyAdic B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsWeaklyAdic B S hS (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  choose A hCR hTS hTR hLT hApres hAwa using fun i ↦ (hP i).2
  let := hCR
  let := hTS
  let := hTR
  let := hLT
  obtain ⟨hsome, K, hK, g, -, hpres⟩ :=
    isPresentingRing_sigma_of_finite B S hS A Z (fun i ↦ (hZaff i).1) hApres
  let : IsLinearTopology (∀ k, A (g k)) (∀ k, A (g k)) :=
    TopologicalRing.pi_isLinearTopology
  let : ∀ k, TopologicalRing.IsWeaklyAdic (A (g k)) := fun k ↦ hAwa (g k)
  exact ⟨hsome, (∀ k, A (g k)), inferInstance, inferInstance, inferInstance,
    TopologicalRing.pi_isLinearTopology, hpres,
    TopologicalRing.isWeaklyAdic_pi fun k ↦ A (g k)⟩

/-- **A coproduct of finitely many adic\* affine formal algebraic spaces is adic\*.** The
presenting ring of the coproduct is the product of presenting rings of the summands; a finite
product of adic topological rings is adic, and the product of finitely generated ideals of
definition of the factors is a finitely generated ideal of definition of the product. -/
theorem isAdicStar_sigma {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) (hZaff : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i))
    (hP : ∀ i, IsAdicStar B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsAdicStar B S hS (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  choose A hCR hTS hTR hLT hApres hAadic hAfg using fun i ↦ (hP i).2
  let := hCR
  let := hTS
  let := hTR
  let := hLT
  choose J hJdef hJfg using hAfg
  obtain ⟨hsome, K, hK, g, -, hpres⟩ :=
    isPresentingRing_sigma_of_finite B S hS A Z (fun i ↦ (hZaff i).1) hApres
  exact ⟨hsome, (∀ k, A (g k)), inferInstance, inferInstance, inferInstance,
    TopologicalRing.pi_isLinearTopology, hpres,
    Rig.isAdic_pi (fun k ↦ A (g k)) fun k ↦ hAadic (g k),
    Ideal.pi fun k ↦ J (g k),
    TopologicalRing.isIdealOfDefinition_pi_ideal _ _ fun k ↦ hJdef (g k),
    Ideal.fg_pi _ fun k ↦ hJfg (g k)⟩

/-- **A coproduct of finitely many Noetherian affine formal algebraic spaces is Noetherian.** The
presenting ring of the coproduct is the product of presenting rings of the summands; a finite
product of Noetherian rings is Noetherian, and a finite product of adic topological rings is
adic. -/
theorem isNoetherian_sigma {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) (hZaff : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i))
    (hP : ∀ i, IsNoetherian B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsNoetherian B S hS (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  choose A hCR hTS hTR hLT hApres hAnoeth hAadic using fun i ↦ (hP i).2
  let := hCR
  let := hTS
  let := hTR
  let := hLT
  obtain ⟨hsome, K, hK, g, -, hpres⟩ :=
    isPresentingRing_sigma_of_finite B S hS A Z (fun i ↦ (hZaff i).1) hApres
  let : ∀ k, IsNoetherianRing (A (g k)) := fun k ↦ hAnoeth (g k)
  exact ⟨hsome, (∀ k, A (g k)), inferInstance, inferInstance, inferInstance,
    TopologicalRing.pi_isLinearTopology, hpres, inferInstance,
    Rig.isAdic_pi (fun k ↦ A (g k)) fun k ↦ hAadic (g k)⟩

end AlgebraicGeometry.FormalSpace

end
