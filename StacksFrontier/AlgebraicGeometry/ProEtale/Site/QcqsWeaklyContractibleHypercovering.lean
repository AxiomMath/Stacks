module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Qcqs
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.Iso

/-!
# Affine weakly contractible hypercoverings of a qcqs object

Every quasi-compact quasi-separated object of a chosen big pro-étale site admits a hypercovering
whose term in each degree is a one-element family on an affine weakly contractible object
covering it.

This is Stacks 09A1 (2). The construction of Stacks 09A1 is run inside the quasi-compact
quasi-separated pro-étale site of
`StacksFrontier/AlgebraicGeometry/ProEtale/Site/Qcqs.lean`, where every object has a one-element
*affine* weakly contractible covering, and the resulting hypercovering is transported to the big
site along the continuous inclusion by Stacks 0DAZ.

## Main results

* `AlgebraicGeometry.ProEtale.QcqsProetale.ofArrows_sigmaι_mem_topology`: the summands of a finite
  disjoint union in a slice of the qcqs site cover it.
* `AlgebraicGeometry.ProEtale.QcqsProetale.isAffine_sigma` and
  `AlgebraicGeometry.ProEtale.QcqsProetale.isWeaklyContractible_sigma`: a finite disjoint union in
  a slice of affine objects is affine, and of objects weakly contractible in the big site is
  weakly contractible there.
* `AlgebraicGeometry.ProEtale.QcqsProetale.exists_affine_weaklyContractible_singleton_cover`:
  every object of the qcqs site has a one-element covering by an affine object which is weakly
  contractible in the big site.
* `AlgebraicGeometry.ProEtale.QcqsProetale.exists_singleton_hypercovering`: the construction of
  Stacks 09A1 run in the qcqs site.
* `AlgebraicGeometry.ProEtale.exists_singleton_affine_weaklyContractible_hypercovering`:
  **Stacks 09A1 (2)**.

## Implementation notes

The class `B` of objects which the construction of Stacks 09A1 is fed is the source's: the
objects of the qcqs site which are affine and weakly contractible. Weak contractibility is that
of the *big* site, as it is in the source and in Stacks 09A1 (1): it is a property of an object of
the ambient pro-étale site, which the construction only ever carries along. Hence the general
form in the namespace `Stacks.CategoryTheory`,
`Hypercovering.exists_singleton_weaklyContractible_hypercovering_of_prop_finiteDisjointUnions`,
is not what instantiates here — its weak contractibility is that of the site being worked in,
which for the qcqs site is a different notion and is not compared to the big site's anywhere in
this library. What is instantiated is the general construction
`Hypercovering.exists_singleton_hypercovering_objects_in_finiteDisjointUnions`, in the same
namespace, with the conjunction of affineness and big-site weak contractibility as its class of
objects, which is exactly the source's `B`.

The one-element affine weakly contractible coverings are Stacks 0F4P in the quasi-compact case,
`AlgebraicGeometry.ProEtale.exists_affine_weaklyContractible_singleton_covering`, whose source is
affine, hence quasi-compact and quasi-separated, hence an object of the qcqs site; this is where
"a finite union of affines is affine" of the source enters, inside the proof of that covering.
A one-element family is finite, so it is a covering family of the qcqs site.

The two hypotheses of Stacks 0DB2 on the degreewise disjoint unions are discharged as in Stacks
09A1 (1): finite coproducts in a slice of the qcqs site are van Kampen because they are in
schemes and the composite functor to schemes preserves finite coproducts and fibre products and
reflects isomorphisms, and taking disjoint unions preserves coverings because the summands of a
finite disjoint union cover it. The weak contractibility and the affineness of a finite disjoint
union are transported from the big site, where the first is
`AlgebraicGeometry.ProEtale.isWeaklyContractible_sigma`.

## References

* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
* [Stacks Project, Tag 0F4P](https://stacks.math.columbia.edu/tag/0F4P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

namespace AlgebraicGeometry.ProEtale

universe u

variable (B : BigProetaleSite.{u})

/-- **The image of a cofan under a functor to schemes which preserves finite coproducts is a
pro-étale covering family.** A finite disjoint union of schemes is covered by its summands in the
Zariski topology, hence in the pro-étale one. -/
theorem ofArrows_map_sigmaι_mem_proetalePrecoverage {C : Type*} [Category C] {I : Type*}
    [Finite I] (G : C ⥤ Scheme.{u}) (A : I → C) [HasCoproduct A] [Small.{u} I]
    [PreservesColimitsOfShape (Discrete I) G] :
    Presieve.ofArrows (fun i ↦ G.obj (A i)) (fun i ↦ G.map (Sigma.ι A i)) ∈
      Scheme.proetalePrecoverage.coverings (G.obj (∐ A)) := by
  have hmap : ∀ i, G.map (Sigma.ι A i) =
      Sigma.ι (fun i ↦ G.obj (A i)) i ≫ (PreservesCoproduct.iso G A).inv := by
    intro i
    rw [PreservesCoproduct.inv_hom]
    exact (ι_comp_sigmaComparison G A i).symm
  simp_rw [hmap]
  refine zariskiPrecoverage_le_proetalePrecoverage _ ?_
  exact ((AlgebraicGeometry.sigmaOpenCover (fun i ↦ G.obj (A i))).pushforwardIso
    (PreservesCoproduct.iso G A).inv).mem₀

namespace QcqsProetale

/-- Finite coproducts in a slice of the qcqs pro-étale site are van Kampen, because they are in
schemes and the functor to schemes preserves them, preserves fibre products and reflects
isomorphisms. -/
instance finitaryExtensive (U : QcqsProetale B) : FinitaryExtensive (Over U) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (Over.forget U ⋙ toScheme B)

section Slice

variable {B}
variable {U : QcqsProetale B} {I : Type (u + 1)} [Finite I] (A : I → Over U)

/-- **The summands of a finite disjoint union in a slice of the qcqs pro-étale site cover it.**
This is the counterpart of `AlgebraicGeometry.ProEtale.ofArrows_sigmaι_mem_topology`, the
finiteness of the family being what makes it a covering family of the qcqs site. -/
theorem ofArrows_sigmaι_mem_topology :
    Sieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (Sigma.ι A i).left) ∈
      topology B ((∐ A : Over U)).left := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  refine ⟨⟨I, fun i ↦ (A i).left, fun i ↦ (Sigma.ι A i).left⟩, rfl, ?_, inferInstance⟩
  exact ofArrows_map_sigmaι_mem_proetalePrecoverage (Over.forget U ⋙ toScheme B) A

/-- **A finite disjoint union of affine objects in a slice of the qcqs pro-étale site is
affine.** -/
theorem isAffine_sigma (hA : ∀ i, IsAffine (A i).left.obj.obj) :
    IsAffine ((∐ A : Over U)).left.obj.obj := by
  have _ (i : I) : IsAffine ((Over.forget U ⋙ toScheme B).obj (A i)) := hA i
  have _ : IsAffine (∐ fun i ↦ (Over.forget U ⋙ toScheme B).obj (A i)) := inferInstance
  exact IsAffine.of_isIso (PreservesCoproduct.iso (Over.forget U ⋙ toScheme B) A).hom

/-- **A finite disjoint union in a slice of the qcqs pro-étale site of objects weakly
contractible in the big site is weakly contractible in the big site.** The disjoint union is
computed in the big site too, the inclusion preserving finite coproducts, so this is
`AlgebraicGeometry.ProEtale.isWeaklyContractible_sigma` transported along that identification. -/
theorem isWeaklyContractible_sigma
    (hA : ∀ i, B.topology.IsWeaklyContractible (A i).left.obj) :
    B.topology.IsWeaklyContractible ((∐ A : Over U)).left.obj := by
  refine GrothendieckTopology.IsWeaklyContractible.of_iso B.topology
    ((PreservesCoproduct.iso (Over.forget U.obj) fun i ↦ (Over.post (inclusion B)).obj (A i)) ≪≫
      (PreservesCoproduct.iso (Over.forget U ⋙ inclusion B) A).symm) ?_
  exact ProEtale.isWeaklyContractible_sigma B
    (fun i ↦ (Over.post (inclusion B)).obj (A i)) hA

end Slice

variable {B}

/-- **Every object of the qcqs pro-étale site has a one-element covering by an affine object
which is weakly contractible in the big site.** This is Stacks 0F4P in the quasi-compact case,
`AlgebraicGeometry.ProEtale.exists_affine_weaklyContractible_singleton_covering`: its source is
affine, hence an object of the qcqs site, and a one-element family is finite, hence a covering
family of the qcqs site. -/
theorem exists_affine_weaklyContractible_singleton_cover (Y : QcqsProetale B) :
    ∃ (V : QcqsProetale B) (f : V ⟶ Y),
      IsAffine V.obj.obj ∧ B.topology.IsWeaklyContractible V.obj ∧
        Presieve.singleton f ∈ (topology B).toPretopology Y := by
  obtain ⟨V₀, p, hcov, haff, hwc⟩ :=
    exists_affine_weaklyContractible_singleton_covering B Y.obj
  have _ : IsAffine V₀.obj := haff
  refine ⟨⟨V₀, ⟨inferInstance, inferInstance⟩⟩, ObjectProperty.homMk p, haff, hwc, ?_⟩
  rw [GrothendieckTopology.mem_toPretopology, ← PreZeroHypercover.presieve₀_singleton]
  exact Precoverage.generate_mem_toGrothendieck ⟨_, rfl, hcov.1, inferInstance⟩

/-- **The construction of Stacks 09A1 in the qcqs pro-étale site.** Every object `U` of it admits
a hypercovering whose term in every degree is the one-element family on an object which is affine,
weakly contractible in the big site, and covers `U`. -/
theorem exists_singleton_hypercovering (U : QcqsProetale B) :
    ∃ K : SimplicialObject (FormalCoproduct.{u + 1} (Over U)),
      IsHypercovering (topology B).toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            IsAffine ((K.obj (op ⦋n⦌)).obj i).left.obj.obj ∧
            B.topology.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left.obj ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈
              (topology B).toPretopology U := by
  obtain ⟨K, hK, hterm⟩ :=
    exists_singleton_hypercovering_objects_in_finiteDisjointUnions (topology B)
      {V : QcqsProetale B | IsAffine V.obj.obj ∧ B.topology.IsWeaklyContractible V.obj} U
      (takeUnionsFinPreservesCoverings_of_ofArrows_sigmaι (topology B) U
        (fun A ↦ ofArrows_sigmaι_mem_topology A))
      (fun A _ hA ↦ ⟨isAffine_sigma A.obj fun k ↦ (hA k).1,
        isWeaklyContractible_sigma A.obj fun k ↦ (hA k).2⟩)
      (fun Y ↦ by
        obtain ⟨V, f, haff, hwc, hf⟩ := exists_affine_weaklyContractible_singleton_cover Y
        exact ⟨PUnit.{u + 2}, fun _ ↦ V, fun _ ↦ f, inferInstance, fun _ ↦ ⟨haff, hwc⟩,
          (ofArrows_pUnit'.{u + 1} f).symm ▸ hf⟩)
  exact ⟨K, hK, fun n ↦ by
    obtain ⟨i, hi, hB, hcov⟩ := hterm n
    exact ⟨i, hi, hB.1, hB.2, hcov⟩⟩

end QcqsProetale

/-- **Stacks Project, Tag 09A1 (2).** Every quasi-compact quasi-separated object `U` of a chosen
big pro-étale site admits a hypercovering each of whose terms is a one-element family on an
affine weakly contractible object of the site covering `U`.

The construction of Stacks 09A1 is run in the quasi-compact quasi-separated pro-étale site, where
the one-element coverings by affine weakly contractible objects of Stacks 0F4P are available, and
the hypercovering obtained there is transported to the big site by Stacks 0DAZ along the
inclusion, which is continuous and preserves fibre products. -/
@[stacks 09A1 "(2), at the library's big pro-etale site"]
theorem exists_singleton_affine_weaklyContractible_hypercovering (U : B.Scheme)
    [CompactSpace U.obj] [QuasiSeparatedSpace U.obj] :
    ∃ K : SimplicialObject (FormalCoproduct.{u + 1} (Over U)),
      IsHypercovering B.topology.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            IsAffine ((K.obj (op ⦋n⦌)).obj i).left.obj ∧
            B.topology.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈
              B.topology.toPretopology U := by
  obtain ⟨K, hK, hterm⟩ :=
    QcqsProetale.exists_singleton_hypercovering (⟨U, ⟨inferInstance, inferInstance⟩⟩ :
      QcqsProetale B)
  refine ⟨K ⋙ mapFormalCoproduct.{u + 1} (Over.post (QcqsProetale.inclusion B)),
    IsHypercovering.map (QcqsProetale.topology B).toPretopology B.topology.toPretopology
      (QcqsProetale.inclusion B) (QcqsProetale.mapsCoveringsToCoverings B) K hK, ?_⟩
  intro n
  obtain ⟨i, hi, haff, hwc, hcov⟩ := hterm n
  refine ⟨i, hi, haff, hwc, ?_⟩
  rw [← ofArrows_pUnit'.{u + 1}] at hcov
  have h := QcqsProetale.mapsCoveringsToCoverings B _ _ hcov
  rwa [ofArrows_pUnit'.{u + 1}] at h

end AlgebraicGeometry.ProEtale

end
