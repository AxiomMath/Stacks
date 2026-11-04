module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech complex of a sheaf of modules is Mathlib's Čech complex

Let `A` be a commutative ring, `f : X ⟶ Spec A` a scheme over the affine base, `F` a sheaf of
`𝒪_X`-modules and `U : I → X.Opens` a family of open subsets. The Čech complex of `F` with
respect to `U` has been built twice: once as a complex of `A`-modules on explicit families of
sections, `Stacks.Cech.cechModuleComplex`, and once categorically, as Mathlib's
`CategoryTheory.cechComplexFunctor` applied to the presheaf of abelian groups underlying `F`.

This file identifies the two as cochain complexes of abelian groups, by composing the
identification `Stacks.Cech.cechModuleComplex_forget` of the module-valued complex with the
Čech complex of Stacks 01FH and the chain-level comparison
`Stacks.Cech.cechComplexIso` of that complex with Mathlib's.

## Main definitions

* `Stacks.Cech.cechModuleComplexIso`: the isomorphism of cochain complexes of abelian groups
  between the `A`-module-valued Čech complex, with its module structures forgotten, and
  Mathlib's Čech complex.
* `Stacks.Cech.alternatingCechModuleComplexToCechComplexFunctor`: the canonical map from the
  alternating Čech complex of `A`-modules, with its module structures forgotten, to Mathlib's
  Čech complex.

## Main results

* `Stacks.Cech.alternatingCechModuleComplex_inclusion_comp_cechModuleComplexIso`: the
  comparison is compatible with the `A`-linear alternating-to-usual inclusion, so the map out
  of the alternating complex really is the transported inclusion of Stacks 01FH.
* `Stacks.Cech.alternatingCechModuleComplexToCechComplexFunctor_homotopyEquivalence`: for a
  linearly ordered index type that map is a homotopy equivalence, which is Stacks 01FM for
  Mathlib's Čech complex.

## Implementation notes

The identification is of complexes of *abelian groups*: the `A`-module structure on the
explicit cochains comes from `Stacks.Cech.baseRingHom`, whereas Mathlib's Čech complex of the
underlying abelian presheaf carries no module structure at all. Producing the comparison
`A`-linearly would require Mathlib's Čech complex of a presheaf of `A`-modules on `X.Opens`,
which is a different functor from the one Stacks 01ET uses (that one lives on the slice
`CategoryTheory.Over V` and is linear over `Γ(X, V)`, not over `A`); the two rings differ by
`Stacks.Cech.globalRingHom`, so that comparison is a restriction of scalars and not an
identity.

Degreewise the first factor of the comparison is `Iso.refl`, by
`Stacks.Cech.cechModuleComplex_forget`, so the composite is degreewise exactly the degreewise
comparison `Stacks.Cech.cechComplexObjIso` of Stacks 01FH.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (F : X.Modules)

/-- **The two Čech complexes of a sheaf of modules agree.** Forgetting the `A`-module
structures, the Čech complex of `F` on explicit families of sections is isomorphic, as a
cochain complex of abelian groups, to Mathlib's `CategoryTheory.cechComplexFunctor` applied to
the presheaf of abelian groups underlying `F`. -/
def cechModuleComplexIso :
    ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechModuleComplex f U F) ≅
      (CategoryTheory.cechComplexFunctor U).obj F.presheaf :=
  cechModuleComplex_forget f U F ≪≫ cechComplexIso U F.presheaf

/-- In each degree the comparison is the degreewise comparison of Stacks 01FH. -/
@[simp]
theorem cechModuleComplexIso_hom_f (p : ℕ) :
    (cechModuleComplexIso f U F).hom.f p = (cechComplexObjIso U F.presheaf p).hom :=
  Category.id_comp _

/-- **The canonical map from the alternating Čech complex of `A`-modules to Mathlib's Čech
complex.** It is the inclusion of the alternating subcomplex of Stacks 01FH followed by the
chain-level comparison. -/
def alternatingCechModuleComplexToCechComplexFunctor :
    ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (alternatingCechModuleComplex f U F) ⟶
      (CategoryTheory.cechComplexFunctor U).obj F.presheaf :=
  (alternatingCechModuleComplex_forget f U F).hom ≫
    alternatingCechInclusionToCechComplexFunctor U F.presheaf

/-- The comparison is compatible with the `A`-linear alternating-to-usual inclusion: the map
to Mathlib's Čech complex out of the alternating complex of `A`-modules is the image of that
inclusion under the comparison. -/
theorem alternatingCechModuleComplex_inclusion_comp_cechModuleComplexIso :
    ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (alternatingCechModuleComplex_inclusion f U F) ≫
        (cechModuleComplexIso f U F).hom =
      alternatingCechModuleComplexToCechComplexFunctor f U F := by
  have key : ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (alternatingCechModuleComplex_inclusion f U F) ≫ (cechModuleComplex_forget f U F).hom =
      (alternatingCechModuleComplex_forget f U F).hom ≫
        alternatingCechInclusion U F.presheaf := by
    rw [← alternatingCechModuleComplex_inclusion_forget f U F, Iso.hom_inv_id_assoc]
  rw [cechModuleComplexIso, alternatingCechModuleComplexToCechComplexFunctor,
    alternatingCechInclusionToCechComplexFunctor, Iso.trans_hom]
  simp only [← Category.assoc]
  rw [key]

/-- **Stacks 01FM for the Čech complex of a sheaf of modules.** For a linearly ordered index
type, the canonical map from the alternating Čech complex of `A`-modules to Mathlib's Čech
complex is a homotopy equivalence. -/
theorem alternatingCechModuleComplexToCechComplexFunctor_homotopyEquivalence [LinearOrder I] :
    (HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.up ℕ))
      (alternatingCechModuleComplexToCechComplexFunctor f U F) := by
  obtain ⟨e, he⟩ :=
    alternatingCechInclusionToCechComplexFunctor_homotopyEquivalence U F.presheaf
  refine ⟨(HomotopyEquiv.ofIso (alternatingCechModuleComplex_forget f U F)).trans e, ?_⟩
  rw [HomotopyEquiv.trans_hom, he]
  rfl

end Stacks.Cech

end

end
