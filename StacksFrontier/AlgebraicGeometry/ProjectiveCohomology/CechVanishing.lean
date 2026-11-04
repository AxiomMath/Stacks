module

public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPushforwardPreservesComparison

/-!
# Vanishing of sheaf cohomology read off the Čech complex

For a covering of an open subset of a scheme all of whose nonempty finite intersections are
affine opens, and a quasi-coherent module, the cohomology over that open vanishes in a degree
exactly when the homology of the *explicit* Čech cochain complex of the covering vanishes in
that degree.

This is the vanishing form of [Stacks, Tag 01XD], which
`Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen` states for the
comparison map of [Stacks, Tag 01EQ]. Its source and target are objects of the bounded-below
derived category: Čech cohomology appears as `H^p` of `DerivedCategory.Plus.Q` of the
extended-by-zero Čech complex, and sheaf cohomology as `H^p` of the derived global sections
`RΓ(U, -)`. Here the first is translated to the homology of the Čech complex and the second to
`Hgroup`, the right derived functor of module-valued sections.

## Main definitions

* `Stacks.Cohomology.CechVanishing.cechPlusHomologyIso`: the Čech cohomology of the covering, as
  the comparison of [Stacks, Tag 01EQ] presents it, is the homology of the Čech cochain complex
  of [Stacks, Tag 01EP].

## Main results

* `Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology`: **the vanishing form
  of [Stacks, Tag 01XD]** — for a covering with affine finite intersections,
  `Hᵖ(U, ℱ) = 0` if and only if the `p`-th homology of the Čech complex of the covering
  vanishes.

## Implementation notes

**The two translations.** On the sheaf-cohomology side the bridge is already in the library and
is general: `Stacks.DerivedIndexing.rightDerivedIso` identifies
`H^p ∘ RF ∘ (-[0])` with the classical `Rᵖ F` for any additive functor out of an abelian
category with enough injectives, and `RΓ(U, -)` of [Stacks, Tag 01EQ] is by definition the first
of those at `F = SheafOfModules.evaluation`. On the Čech side the bridge is
`DerivedCategory.homologyFunctorFactors` followed by
`HomologicalComplex.extendHomologyIso`, because the complex fed to the derived category is the
extension by zero along `ComplexShape.embeddingUpNat` of the `ℕ`-indexed Čech complex, and
extension by zero does not change homology in the degrees it covers.

**The `Hgroup` translation.** The classical right derived functor of
`SheafOfModules.evaluation` vanishes exactly when `Hgroup` does, by
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`.

**No `rw` is used to compose the four steps.** The `Hgroup` translation is stated for a sheaf of
rings on an arbitrary topological space, and rewriting with it against a goal mentioning
`X.ringCatSheaf` fails: the `TopologicalSpace` instance on `↥X` and the one carried by
`X.toPresheafedSpace` are not syntactically equal, and `rw` reports a pattern mismatch with an
application type error underneath. The four `Iff`s are therefore composed in term mode with
`Iff.trans`, which forms no rewrite motive.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

universe u

namespace Stacks.Cohomology.CechVanishing

attribute [local instance] HasDerivedCategory.standard

section Translation

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- **Čech cohomology as presented by [Stacks, Tag 01EQ] is the homology of the Čech cochain
complex of [Stacks, Tag 01EP].** The complex handed to the derived category is the extension by
zero of the `ℕ`-indexed Čech complex along `ComplexShape.embeddingUpNat`, so the identification
is the derived-category homology factorisation followed by
`HomologicalComplex.extendHomologyIso`. -/
public noncomputable def cechPlusHomologyIso (U : Opens X) {I : Type u} (Ui : I → Opens X)
    (hU : U = ⨆ i, Ui i) (F : SheafOfModules.{u} R) (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (SectionRing R U)) (p : ℤ)).obj
        (DerivedCategory.Plus.Q.obj ((cechComplexPlusFunctor R U Ui hU).obj F)) ≅
      (cechComplex.{u, u, u, u} U Ui hU F).homology p :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (SectionRing R U)) (p : ℤ)).app
      ((cechComplexIntFunctor R U Ui hU).obj F) ≪≫
    HomologicalComplex.extendHomologyIso (cechComplex.{u, u, u, u} U Ui hU F)
      ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) (by simp)

end Translation

/-- **The vanishing form of [Stacks, Tag 01XD].** Let `Ui` be a covering of an open subset `U` of
a scheme whose nonempty finite intersections are all affine opens, and let `ℱ` be a quasi-coherent
module. Then `Hᵖ(U, ℱ)` vanishes exactly when the `p`-th homology of the Čech cochain complex of
the covering vanishes. -/
public theorem isZero_Hgroup_iff_isZero_cechHomology
    (Y : Scheme.{u}) {I : Type u} (U : Y.Opens) (Ui : I → Y.Opens) (hU : U = ⨆ i, Ui i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, Ui (s k)))
    (F : Y.Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsZero (Hgroup Y.ringCatSheaf U p F) ↔
      IsZero ((cechComplex.{u, u, u, u} U Ui hU F).homology p) :=
  have hiso : IsIso ((cechCohomologyToCohomology Y.ringCatSheaf U Ui hU (p : ℤ)).app F) :=
    Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen Y U Ui hU
      haffine F p
  (CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup Y.ringCatSheaf U p F).symm.trans
    ((((Stacks.DerivedIndexing.rightDerivedIso
        (SheafOfModules.evaluation.{u} Y.ringCatSheaf (op U)) p).app F).symm.isZero_iff).symm.trans
      (((@asIso _ _ _ _ ((cechCohomologyToCohomology Y.ringCatSheaf U Ui hU (p : ℤ)).app F)
          hiso).isZero_iff).symm.trans
        (cechPlusHomologyIso Y.ringCatSheaf U Ui hU F p).isZero_iff))

end Stacks.Cohomology.CechVanishing

end
