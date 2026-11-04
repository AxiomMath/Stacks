module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer

/-!
# Leray's acyclicity lemma for derived sections over a base ring

Let `(X, 𝒪_X)` be a ringed space, let `ρ : B ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative
ring, and let `RΓ(X, -) : D(𝒪_X) ⥤ D(B)` be the unbounded derived functor of `B`-linear global
sections, `Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver`. For a cochain complex
`K` of sheaves of `𝒪_X`-modules there is a canonical comparison
$$ Q(\Gamma(X, K^\bullet)) \longrightarrow R\Gamma(X, Q(K^\bullet)) $$
in `D(B)`, and this file proves it invertible when `K` is bounded below and each of its terms has
vanishing higher cohomology on `X`.

This is Leray's acyclicity lemma, [Stacks, Tag 015E], in the form in which the cohomology of a
complex of sheaves of modules is computed by its complex of global sections. Acyclicity of a term
follows from the vanishing of its cohomology groups `Hⁿ(X, -)` of [Stacks, Tag 01E3].

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOverBase.sectionsOverComplexComparison`: the comparison
  `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))`, as a natural transformation.
* `Stacks.Cohomology.DerivedSectionsOverBase.sectionsOverComplexIso`: the resulting isomorphism
  at a bounded below complex with acyclic terms.

## Main results

* `Stacks.Cohomology.DerivedSectionsOverBase.isZero_rightDerived_sectionsOver_of_isZero_hgroup`:
  the higher right derived functors of `B`-linear global sections vanish where the cohomology
  groups do.
* `Stacks.Cohomology.DerivedSectionsOverBase.rightAcyclic_sectionsOver_of_isZero_hgroup`: a sheaf
  of modules whose higher cohomology groups over the whole space vanish is right acyclic for
  `B`-linear global sections.
* `Stacks.Cohomology.DerivedSectionsOverBase.isIso_sectionsOverComplexComparison_app`:
  **Leray's acyclicity lemma**, the comparison is invertible.

## Implementation notes

`HasDerivedCategory.standard` is given a high priority rather than merely declared a local
instance: the derived categories in the statement of
`Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver` are baked at that model, and a
competing instance in scope would silently produce a different one.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)

universe u

namespace Stacks.Cohomology.DerivedSectionsOverBase

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) {B : Type u} [CommRing B]
  (ρ : B →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))

/-! ### Acyclicity from the vanishing of cohomology groups -/

/-- **The higher right derived functors of `B`-linear global sections vanish where the cohomology
groups do.** If `Hᵖ(X, F)` is zero then so is the `p`-th right derived functor of
`Γ(X, -) : Mod(𝒪_X) ⥤ Mod(B)` at `F`. -/
theorem isZero_rightDerived_sectionsOver_of_isZero_hgroup (p : ℕ)
    (F : SheafOfModules.{u} (structureSheafRing X))
    (h : IsZero (Hgroup (structureSheafRing X) ⊤ p F)) :
    IsZero (((sectionsOver X ρ).rightDerived p).obj F) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (sectionsOverOpen X ⊤) (ModuleCat.restrictScalars.{u} ρ) p F
  have h' : IsZero (((SheafOfModules.evaluation (structureSheafRing X)
      (op (⊤ : Opens X.carrier))).rightDerived p).obj F) :=
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      (structureSheafRing X) ⊤ p F).2 h
  exact (Functor.map_isZero (ModuleCat.restrictScalars.{u} ρ) h').of_iso e.symm

/-- **A sheaf of modules with no higher cohomology on `X` is right acyclic for `B`-linear global
sections.** -/
theorem rightAcyclic_sectionsOver_of_isZero_hgroup
    (F : SheafOfModules.{u} (structureSheafRing X))
    (h : ∀ p : ℕ, 0 < p → IsZero (Hgroup (structureSheafRing X) ⊤ p F)) :
    (sectionsOver X ρ).rightAcyclic F :=
  (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived (sectionsOver X ρ) F).2
    fun p hp => isZero_rightDerived_sectionsOver_of_isZero_hgroup X ρ p F (h p hp)

/-! ### The comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` -/

/-- **The canonical comparison from the complex of `B`-linear global sections of a complex of
`𝒪_X`-modules to the derived global sections of the object it represents in `D(𝒪_X)`.** -/
def sectionsOverComplexComparison :
    (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSectionsOver X ρ :=
  Stacks.DerivedAcyclic.complexDerivedUnit (sectionsOver X ρ) (derivedSectionsOver X ρ)
    (derivedSectionsOverUnit X ρ)

/-- **Leray's acyclicity lemma for derived sections over a base ring**, [Stacks, Tag 015E]. Let
`K` be a bounded below cochain complex of sheaves of `𝒪_X`-modules each of whose terms is right
acyclic for `B`-linear global sections. Then the comparison
`Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` is invertible: the complex of global sections of `K` already computes
the unbounded derived global sections of `K`. -/
theorem isIso_sectionsOverComplexComparison_app
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : CochainComplex.plus _ K)
    (hac : ∀ n : ℤ, (sectionsOver X ρ).rightAcyclic (K.X n)) :
    IsIso ((sectionsOverComplexComparison X ρ).app K) := by
  have h := Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic (sectionsOver X ρ)
    (derivedSectionsOver X ρ) (derivedSectionsOverUnit X ρ) K hK hac
  have := h
  dsimp [sectionsOverComplexComparison, Stacks.DerivedAcyclic.complexDerivedUnit]
  infer_instance

/-- **The complex of global sections of a bounded below complex with acyclic terms is its derived
global sections**, as an isomorphism of `D(B)`. -/
def sectionsOverComplexIso
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : CochainComplex.plus _ K)
    (hac : ∀ n : ℤ, (sectionsOver X ρ).rightAcyclic (K.X n)) :
    DerivedCategory.Q.obj (((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (derivedSectionsOver X ρ).obj (DerivedCategory.Q.obj K) :=
  @asIso _ _ _ _ _ (isIso_sectionsOverComplexComparison_app X ρ K hK hac)

end Stacks.Cohomology.DerivedSectionsOverBase

end
