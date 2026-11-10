module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Big
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.WeaklyContractibleOneElementCovers
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.WeaklyContractibleHypercovering

/-!
# Weakly contractible hypercoverings in a big pro-étale site

Every object of a chosen big pro-étale site admits a hypercovering whose term in each degree is
a one-element family on a weakly contractible object covering that object.

## Main results

* `AlgebraicGeometry.ProEtale.ofArrows_sigmaι_mem_topology`: the summands of a finite disjoint
  union in a slice of the site cover it.
* `AlgebraicGeometry.ProEtale.isWeaklyContractible_sigma`: a finite disjoint union of weakly
  contractible objects of a slice is weakly contractible.
* `AlgebraicGeometry.ProEtale.exists_singleton_weaklyContractible_hypercovering_unconditional`:
  the existence of such a hypercovering, with nothing carried.
* `AlgebraicGeometry.ProEtale.exists_singleton_weaklyContractible_hypercovering`: the same
  existence statement, with the hypotheses of Stacks 0DB2 carried for the callers that pass
  them.

## Implementation notes

The one-element coverings by weakly contractible objects come from Stacks 0F4P,
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering`, in the shape it
delivers them: a chosen covering family `PreZeroHypercover.singleton p` together with weak
contractibility of its source. They are converted here into membership of the one-element
presieve in the pretopology attached to the topology of the site, which is what the
construction of Stacks 09A1 consumes.

The construction of Stacks 09A1 takes disjoint unions degreewise, and the hypotheses that
Stacks 0DB2 makes on them are discharged here for the finite families the construction
produces. Two of them are instances: the underlying category of the site is closed under finite
coproducts, because the cutoff is closed under at most countable coproducts by Stacks 000R (2),
and
finite coproducts in a slice are van Kampen, because they are in schemes and the forgetful
functor to schemes preserves finite coproducts and fibre products and reflects isomorphisms.
The remaining one, that taking disjoint unions preserves coverings, is reduced by
`Stacks.CategoryTheory.Hypercovering.takeUnionsFinPreservesCoverings_of_ofArrows_sigmaι` to the
statement that the summands of a finite disjoint union cover it, which holds because a finite
disjoint union of schemes is covered by its summands in the Zariski topology.

The weak contractibility of a finite disjoint union of weakly contractible objects is the
argument of Stacks 0F4P reused: the summands cover the union, they are pairwise disjoint
because distinct summands of a finite coproduct in an extensive category meet in an initial
object, whose underlying scheme is empty, so a sheaf takes the union to the product of its
values on the summands and a product of surjections of sets is surjective.

## References

* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
* [Stacks Project, Tag 0F4P](https://stacks.math.columbia.edu/tag/0F4P)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})

/-! ### Finite coproducts in a chosen big pro-étale site -/

private instance small_of_finite (I : Type*) [Finite I] : Small.{u} I := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  exact small_map e

/-- **The size cutoff of a chosen big pro-étale site is closed under finite coproducts of
schemes**, in the form Mathlib uses to equip a full subcategory with finite coproducts. The
cutoff is closed under at most countable coproducts by Stacks 000R (2), which is more than a
finite index type needs. -/
instance isClosedUnderFiniteCoproducts :
    (boundedSchemeProperty B.cutoff).IsClosedUnderFiniteCoproducts := by
  refine ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape ?_
  intro J _
  exact AlgebraicGeometry.schemeSizeBelow_isClosedUnderColimitsOfShape_discrete
    B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0

/-- The bounded category of a chosen big pro-étale site has finite coproducts, and in particular
an initial object: the empty scheme. -/
instance hasFiniteCoproducts : HasFiniteCoproducts B.Scheme := inferInstance

/-- Finite coproducts in a slice of a chosen big pro-étale site are van Kampen, because they are
in schemes and the forgetful functor to schemes preserves them, preserves fibre products and
reflects isomorphisms. -/
instance finitaryExtensive (U : B.Scheme) : FinitaryExtensive (Over U) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (Over.forget U ⋙ B.inclusion)

/-! ### Finite disjoint unions in a slice -/

section Slice

variable {U : B.Scheme} {I : Type*} [Finite I] (A : I → Over U)

/-- The underlying schemes of a family of objects of a slice of a chosen big pro-étale site. -/
private def sliceLeft (i : I) : Scheme.{u} := B.inclusion.obj (A i).left

/-- The underlying scheme of a finite disjoint union in a slice, as a coproduct of schemes. -/
private noncomputable def sliceSigmaIso :
    B.inclusion.obj ((∐ A : Over U)).left ≅ ∐ sliceLeft B A :=
  PreservesCoproduct.iso (Over.forget U ⋙ B.inclusion) A

/-- A summand inclusion of a finite disjoint union in a slice is, as a morphism of schemes, a
summand inclusion of the corresponding coproduct of schemes. -/
private theorem map_sigmaι (i : I) :
    B.inclusion.map ((Sigma.ι A i).left) =
      Sigma.ι (sliceLeft B A) i ≫ (sliceSigmaIso B A).inv := by
  change _ = Sigma.ι (sliceLeft B A) i ≫
    (PreservesCoproduct.iso (Over.forget U ⋙ B.inclusion) A).inv
  rw [PreservesCoproduct.inv_hom]
  exact (ι_comp_sigmaComparison (Over.forget U ⋙ B.inclusion) A i).symm

/-- **The summands of a finite disjoint union in a slice cover it.** A finite disjoint union of
schemes is covered by its summands in the Zariski topology, hence in the pro-étale one. -/
theorem ofArrows_sigmaι_mem_topology :
    Sieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (Sigma.ι A i).left) ∈
      B.topology ((∐ A : Over U)).left := by
  apply Precoverage.generate_mem_toGrothendieck
  rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  change Presieve.ofArrows (sliceLeft B A) (fun i ↦ B.inclusion.map ((Sigma.ι A i).left)) ∈ _
  simp_rw [map_sigmaι B A]
  refine zariskiPrecoverage_le_proetalePrecoverage _ ?_
  exact ((AlgebraicGeometry.sigmaOpenCover
    (sliceLeft B A)).pushforwardIso (sliceSigmaIso B A).inv).mem₀

/-- A summand inclusion of a finite disjoint union in a slice is a monomorphism, because the
summand inclusions of a finite coproduct are. -/
theorem mono_sigmaι_left (i : I) : Mono ((Sigma.ι A i).left) := by
  exact Over.mono_left_of_mono (Sigma.ι A i)

/-- An object mapping compatibly into two distinct summands of a finite disjoint union in a
slice is covered by the empty sieve: distinct summands of a finite coproduct are disjoint, so
such an object is initial, hence has empty underlying scheme. -/
theorem bot_mem_topology_of_factors {i j : I} (hij : i ≠ j) (Z : B.Scheme)
    (a : Z ⟶ (A i).left) (b : Z ⟶ (A j).left)
    (hab : a ≫ (Sigma.ι A i).left = b ≫ (Sigma.ι A j).left) :
    (⊥ : Sieve Z) ∈ B.topology Z := by
  have hw : b ≫ (A j).hom = a ≫ (A i).hom := by
    rw [← Over.w (Sigma.ι A j), ← Category.assoc, ← hab, Category.assoc, Over.w]
  let Z' : Over U := Over.mk (a ≫ (A i).hom)
  have hab' : (Over.homMk a : Z' ⟶ A i) ≫ Sigma.ι A i =
      (Over.homMk b hw : Z' ⟶ A j) ≫ Sigma.ι A j :=
    Over.OverMorphism.ext (by simpa using hab)
  have hd := FinitaryExtensive.isPullback_initial_to_sigma_ι A i j hij
  have _ := HasStrictInitialObjects.out (hd.lift _ _ hab') initialIsInitial
  have hZ' : IsInitial Z' := IsInitial.ofIso initialIsInitial (asIso (hd.lift _ _ hab')).symm
  have _ : IsEmpty (B.inclusion.obj Z) :=
    AlgebraicGeometry.isInitial_iff_isEmpty.mp
      ⟨(hZ'.isInitialObj (Over.forget U)).isInitialObj B.inclusion⟩
  rw [← Sieve.generate_bot]
  apply Precoverage.generate_mem_toGrothendieck
  rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_bot]
  exact Scheme.bot_mem_propQCPrecoverage (P := @WeaklyEtale) _

/-- **A finite disjoint union of weakly contractible objects of a slice is weakly
contractible.** -/
theorem isWeaklyContractible_sigma
    (hA : ∀ i, B.topology.IsWeaklyContractible (A i).left) :
    B.topology.IsWeaklyContractible ((∐ A : Over U)).left :=
  B.topology.isWeaklyContractible_of_disjointCover (fun i ↦ (A i).left)
    (fun i ↦ (Sigma.ι A i).left) (ofArrows_sigmaι_mem_topology B A) (mono_sigmaι_left B A)
    (fun _ _ hij ↦ bot_mem_topology_of_factors B A hij) hA

end Slice

/-- A chosen one-element covering family of a big pro-étale site gives a one-element covering
presieve of the pretopology attached to its topology. -/
theorem singleton_mem_toPretopology_of_covering {U V : B.Scheme} (p : V ⟶ U)
    (hp : B.covering ⟨U, PreZeroHypercover.singleton p⟩) :
    Presieve.singleton p ∈ B.topology.toPretopology U := by
  rw [GrothendieckTopology.mem_toPretopology, BigProetaleSite.mem_topology_iff]
  refine ⟨PreZeroHypercover.singleton p, hp, ?_⟩
  rintro Y _ ⟨_⟩
  exact Sieve.le_generate _ _ _ Presieve.singleton.mk

/-- **Stacks Project, Tag 09A1 (1).** Every object `U` of a chosen big pro-étale site admits a
hypercovering each of whose terms is a one-element family on a weakly contractible object of the
site covering `U`.

The one-element coverings by weakly contractible objects are those of Stacks 0F4P, supplied by
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering`. The two hypotheses on
disjoint unions are discharged here: that taking finite disjoint unions preserves coverings
because the summands of a finite disjoint union cover it, and that a finite disjoint union of
weakly contractible objects is weakly contractible. -/
@[stacks 09A1 "(1), at the library's big pro-etale site"]
theorem exists_singleton_weaklyContractible_hypercovering_unconditional (U : B.Scheme) :
    ∃ K : SimplicialObject (FormalCoproduct.{u + 1} (Over U)),
      IsHypercovering B.topology.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            B.topology.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈
              B.topology.toPretopology U := by
  refine exists_singleton_weaklyContractible_hypercovering_finiteDisjointUnions
    B.topology U
    (takeUnionsFinPreservesCoverings_of_ofArrows_sigmaι B.topology U
      (fun A ↦ ofArrows_sigmaι_mem_topology B A))
    (fun A _ hA ↦ isWeaklyContractible_sigma B A.obj hA) (fun T ↦ ?_)
  obtain ⟨V, p, hcov, hwc⟩ := exists_weaklyContractible_singleton_covering B T
  exact ⟨V, p, hwc, singleton_mem_toPretopology_of_covering B p hcov⟩

/-- **Stacks Project, Tag 09A1 (1).** Every object `U` of a chosen big pro-étale site admits a
hypercovering each of whose terms is a one-element family on a weakly contractible object of the
site covering `U`.

The one-element coverings by weakly contractible objects are those of Stacks 0F4P, supplied by
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering`; the hypotheses on
disjoint unions are discharged as in
`exists_singleton_weaklyContractible_hypercovering_unconditional`. -/
@[stacks 09A1 "(1), at the library's big pro-etale site. The one-element weakly contractible \
covering is Tag 0F4P, discharged here; the three instance hypotheses are \
Tag 0DB2's own hypotheses, propagated"]
theorem exists_singleton_weaklyContractible_hypercovering (U : B.Scheme)
    [HasFiniteCoproducts (Over U)]
    [ObjectProperty.IsClosedUnderFiniteLimits
      (fun A : FormalCoproduct.{u + 1} (Over U) ↦ HasCoproduct A.obj)]
    [PreservesFiniteLimits (takeUnions.{u + 1, u, u + 1} (C := Over U))] :
    ∃ K : SimplicialObject (FormalCoproduct.{u + 1} (Over U)),
      IsHypercovering B.topology.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            B.topology.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈
              B.topology.toPretopology U :=
  exists_singleton_weaklyContractible_hypercovering_unconditional B U

end AlgebraicGeometry.ProEtale

end
