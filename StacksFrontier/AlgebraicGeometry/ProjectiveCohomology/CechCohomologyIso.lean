module

public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison

/-!
# Čech cohomology of an affine covering is sheaf cohomology, as an isomorphism

For a covering of an open subset of a scheme all of whose finite intersections are affine opens,
and a quasi-coherent module, [Stacks, Tag 01XD] says that the canonical comparison from Čech
cohomology to sheaf cohomology is an isomorphism. What the library records of this is the
*vanishing* consequence: `Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology`
is an `Iff` between `Hᵖ(U, ℱ) = 0` and the vanishing of the `p`-th homology of the explicit Čech
cochain complex of [Stacks, Tag 01EP]. Every ingredient of that `Iff` is an isomorphism, so the
isomorphism itself is available; this file writes it down.

The statement is made for the *module-valued* cohomology, the right derived functor of
`Stacks.Cohomology.sectionsFunctor`, which is what carries the `Γ(X, U)`-module structure. No
forgetful functor appears: the explicit Čech complex
`Stacks.Cohomology.CechSheaf.cechComplex` is already a complex of `Γ(X, U)`-modules and the
three isomorphisms composed below are isomorphisms of such. This matters for a consumer that
needs the cohomology of a quasi-coherent module *as a module* rather than as an abelian group —
for instance the cohomology of a twist on projective space over a ring, which the source states
as an isomorphism of `R`-modules.

Specialized to the standard coordinate covering of `Proj R[T₀, …, Tₙ]` and to a twist `𝒪(d)`,
this is the isomorphism whose vanishing shadow is
`Stacks.ProjectiveCohomology.isZero_Hgroup_twistingSheaf_iff`.

## Main definitions

* `Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived`: **the cohomology of a quasi-coherent
  module over an open subset is the homology of the explicit Čech complex of a covering with
  affine finite intersections**, as `Γ(X, U)`-modules.
* `Stacks.ProjectiveCohomology.cechHomologyIsoRightDerivedTwistingSheaf`: **the cohomology of a
  twist `𝒪(d)` on `Proj R[T₀, …, Tₙ]` is the homology of the explicit Čech complex of the
  `n + 1` standard coordinate opens**, in every degree and for every coefficient ring.

## Implementation notes

**What is composed.** Three isomorphisms, read from the derived functor to the homology of the
Čech complex:

* `Stacks.DerivedIndexing.rightDerivedIso`, which identifies the classical right
  derived functor with its derived-category spelling;
* `Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen`, which is
  [Stacks, Tag 01XD] and supplies `IsIso` of the comparison of [Stacks, Tag 01EQ], turned into
  an isomorphism by `CategoryTheory.asIso`;
* `Stacks.Cohomology.CechVanishing.cechPlusHomologyIso`, which identifies the homology of the
  image of the Čech complex in the bounded-below derived category with the homology of the
  explicit `ℕ`-indexed Čech complex.

The middle step lands in `Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor` composed
with a homology functor, which is `CategoryTheory.Functor.rightDerivedPlus` of
`Stacks.Cohomology.sectionsFunctor` up to reassociation of composites; that reassociation is
definitional on objects, so no comparison appears for it.

**Why the abelian-group spelling is not restated here.** `Hgroup` is by definition a right
derived functor of the abelian-group-valued sections functor, so relating it to the module-valued
one costs a forgetful functor and loses the module structure, which is the thing the statement
above exists to keep. The vanishing translation between the two spellings is already proved, as
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`.

**The passage to the ordered complex is proved elsewhere and is not restated here either.** The source
computes with the *ordered* Čech complex, one term per strictly increasing tuple of indices,
whereas `Stacks.Cohomology.CechSheaf.cechComplex` has one term per tuple. The two have the same
homology, as abelian groups, by `Stacks.Cech.orderedCechHomologyIso` composed with
`Stacks.Cech.alternatingCechHomologyIso` and
`Stacks.Cohomology.CechSheaf.alternatingCechHomologyIso`. The forgetful functor is unavoidable
there for a mathematical reason: [Stacks, Tag 01FM] is proved by sorting permutations of the
index tuples, which is additive but not linear over the ring of sections.

**`Stacks.Cohomology.sectionsFunctor` rather than `SheafOfModules.evaluation`.** The two are
the same by definition, but the bare name `SheafOfModules.evaluation` is ambiguous in this
import context — `Stacks.SheafOfModules.evaluation`, the evaluation pairing `F∨ ⊗ F ⟶ 𝒪_X` of a
sheaf of modules on a ringed space, is also in scope and takes a presheaf of commutative rings
as its first argument, so the bare name resolves to it and the statement does not elaborate.

**The index type is in the universe of the scheme.** [Stacks, Tag 01XD] quantifies over a
covering indexed by a type in the universe of the scheme, and the explicit Čech cochain complex
is a product over tuples of indices, so the index universe cannot be left free. This is why
`I : Type u` rather than `I : Type*`.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.CechIso

/-- **The cohomology of a quasi-coherent module is the homology of the explicit Čech complex of a
covering with affine finite intersections**, as `Γ(X, U)`-modules. This is [Stacks, Tag 01XD] in
the shape its consumers want: the module-valued right derived functor of sections on one side
and the Čech cochain complex of [Stacks, Tag 01EP] on the other. -/
public noncomputable def cechHomologyIsoRightDerived (X : Scheme.{u}) {I : Type u} (U : X.Opens)
    (Ui : I → X.Opens) (hU : U = ⨆ i, Ui i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, Ui (s k)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    ((Stacks.Cohomology.sectionsFunctor X U).rightDerived p).obj F ≅
      (cechComplex.{u, u, u, u} U Ui hU F).homology p :=
  have hiso : IsIso ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).app F) :=
    Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen X U Ui hU
      haffine F p
  (Stacks.DerivedIndexing.rightDerivedIso (Stacks.Cohomology.sectionsFunctor X U) p).app F ≪≫
    (@asIso _ _ _ _ ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).app F)
      hiso).symm ≪≫
      Stacks.Cohomology.CechVanishing.cechPlusHomologyIso X.ringCatSheaf U Ui hU F p

end Stacks.Cohomology.CechIso

namespace Stacks.ProjectiveCohomology

variable (R : Type u) [CommRing R]

/-- **The cohomology of a twist `𝒪(d)` on `Proj R[T₀, …, Tₙ]` is the homology of the explicit
Čech complex of the `n + 1` standard coordinate opens**, as modules over the ring of global
sections, in every degree and for every coefficient ring. This is the isomorphism whose
vanishing shadow is `Stacks.ProjectiveCohomology.isZero_Hgroup_twistingSheaf_iff`. -/
public noncomputable def cechHomologyIsoRightDerivedTwistingSheaf (n : ℕ) (d : ℤ) (q : ℕ) :
    ((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).rightDerived q).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) ≅
      (cechComplex.{u, u, u, u}
        (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
        (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)).homology q :=
  @Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived
    (AlgebraicGeometry.Proj (polyGrading R n)) _ ⊤ (basicOpenXAtUniverse R n)
    (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse R n r s) _
    (isQuasicoherent_twistingSheaf R n d) q

end Stacks.ProjectiveCohomology

end
