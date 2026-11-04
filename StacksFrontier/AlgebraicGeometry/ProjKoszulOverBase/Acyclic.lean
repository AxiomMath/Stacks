module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Locality
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.Exactness
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.LocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# The Koszul resolution of the structure sheaf stays acyclic under every base change

Let `A` be a commutative ring and `n` a natural number. The Koszul complex of the coordinates on
`ℙⁿ_A = Proj A[T₀, …, Tₙ]`,

`0 ⟶ 𝒪(a) ⟶ 𝒪(a+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ 𝒪(a+n+1) ⟶ 0`,

is acyclic (`Stacks.AlgebraicGeometry.ProjKoszulComplex.acyclic_koszulComplex`). This file proves
that its **termwise inverse image along an arbitrary morphism of schemes `g : X ⟶ ℙⁿ_A` is
acyclic again** — with no flatness hypothesis on `g`.

A bounded above complex of flat modules is K-flat ([Stacks, Tag 06YQ]) and the termwise inverse
image of an acyclic K-flat complex is acyclic ([Stacks, Tag 06YW]). The terms of the Koszul
complex are flat: each is a finite direct sum of twists, and a twist on `Proj` of a ring
generated in degree one is invertible, hence flat.

## Main results

* `Stacks.AlgebraicGeometry.ProjKoszulOverBase.isFlat_twistingSheaf`: **a twist on
  `ℙⁿ_A` is flat.**
* `Stacks.AlgebraicGeometry.ProjKoszulOverBase.isFlat_koszulTerm`: **every term of the Koszul
  complex is flat**, being a finite direct sum of twists.
* `Stacks.AlgebraicGeometry.ProjKoszulOverBase.kFlat_koszulComplex`: **the Koszul complex is
  K-flat**, being bounded above with flat terms.
* `Stacks.AlgebraicGeometry.ProjKoszulOverBase.acyclic_pullback_koszulComplex`: **the termwise
  inverse image of the Koszul complex along an arbitrary morphism of schemes into `ℙⁿ_A` is
  acyclic.**

## Implementation notes

The terms are `⨁ koszulFamily A n a j`, a *biproduct* over the index type
`Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulIndex (n+1) j` of subsets of the coordinates,
which lies in `Type 0`; flatness of a finite direct sum is available for a *coproduct* whose
index type lies in the universe of the sections. Both gaps are crossed by one isomorphism,
`CategoryTheory.Limits.Sigma.whiskerEquiv` along `Equiv.ulift` followed by
`CategoryTheory.Limits.biproduct.isoCoproduct`, and transported by
`Stacks.SheafOfModules.FlatRetract.isFlat_of_iso`.

The ring sheaf is spelled `AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮` and not
`(AlgebraicGeometry.Proj 𝒮).sheaf`. The two are definitionally equal, but the second presents the
site as the opens of `↥(Proj 𝒮)` rather than of `ProjectiveSpectrum.top 𝒮`, which is the spelling
the twisting sheaves and the Koszul complex live on; unifying the two inside the flatness lemmas
exhausts the heartbeat budget. The ringed space of `Proj 𝒮` is therefore named explicitly where
the invertibility input asks for one.

Flatness of the twists needs the polynomial ring to be generated in degree one over its
degree-zero part, which is
`Stacks.AlgebraicGeometry.ProjKoszulComplex.adjoin_degree_one_polyGrading`, in the form
`Set.range` rather than the coercion of the submodule that
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_adjoin_degree_one`
asks for; the two sets are equal by `Set.ext`.

The conclusion is stated for a morphism of **schemes** and `AlgebraicGeometry.Scheme.Modules`;
`AlgebraicGeometry.pullback_scheme_eq` identifies that functor with the ringed-space
`RingedSpaceModuleAdjunction.modulePullback` of the underlying morphism, by `rfl`, so the
ringed-space statement applies with no comparison.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YW](https://stacks.math.columbia.edu/tag/06YW)
* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.ProjKoszulOverBase

open Stacks.AlgebraicGeometry.ProjKoszulComplex
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
  (isInvertible_twistingSheaf_of_adjoin_degree_one)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **A twist of the structure sheaf of `ℙⁿ_A` is flat.** -/
theorem isFlat_twistingSheaf (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n))
      (twistingSheaf (polyGrading A n) d) := by
  refine Stacks.SheafOfModules.isFlat_of_isInvertible
    (X := Stacks.SchemeCohomology.ringedSpace (AlgebraicGeometry.Proj (polyGrading A n))) _ ?_
  refine isInvertible_twistingSheaf_of_adjoin_degree_one (polyGrading A n) ?_ d
  refine Eq.trans (congrArg (Algebra.adjoin (polyGrading A n 0)) ?_)
    (adjoin_degree_one_polyGrading A n)
  ext p
  simp

/-- **Every term of the Koszul complex of the coordinates on `ℙⁿ_A` is flat**: it is a finite
direct sum of twists, each of which is flat. -/
theorem isFlat_koszulTerm (a j : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n))
      (koszulTerm A n a j) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso
    (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n))
    (Sigma.whiskerEquiv (Equiv.ulift (α := koszulIndex (n + 1) j))
        (fun _ => Iso.refl (twistingSheaf (polyGrading A n) (a + j))) ≪≫
      (biproduct.isoCoproduct (koszulFamily A n a j)).symm)
    (Stacks.SheafOfModules.FlatColimits.isFlat_coproduct_finite
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n))
      (fun _ : ULift.{u} (koszulIndex (n + 1) j) => twistingSheaf (polyGrading A n) (a + j))
      fun _ => isFlat_twistingSheaf A n (a + j))

/-- **The Koszul complex of the coordinates on `ℙⁿ_A` is K-flat** ([Stacks, Tag 06YQ]): it is
concentrated in the degrees `0, …, n + 1`, hence bounded above, and its terms are flat. -/
theorem kFlat_koszulComplex (a : ℤ) :
    Stacks.SheafOfModules.IsKFlat (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n))
      (koszulComplex A n a) :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat
    (R := ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n)) (koszulComplex A n a)
    ⟨(n : ℤ) + 1, Stacks.AlgebraicGeometry.ExampleGenerator.isStrictlyLE_koszulComplex A n a⟩
    fun j => isFlat_koszulTerm A n a j

/-- **The Koszul resolution of the structure sheaf of `ℙⁿ_A` stays acyclic under every base
change.** For an arbitrary morphism of schemes `g : X ⟶ ℙⁿ_A` — no flatness assumed — the
termwise inverse image

`0 ⟶ g^*𝒪(a) ⟶ g^*𝒪(a+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ g^*𝒪(a+n+1) ⟶ 0`

is acyclic. -/
theorem acyclic_pullback_koszulComplex {X : Scheme.{u}}
    (g : X ⟶ AlgebraicGeometry.Proj (polyGrading A n)) (a : ℤ) :
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (koszulComplex A n a)).Acyclic :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.acyclic_pullback_of_kFlat_of_acyclic
    (Stacks.SchemeCohomology.hom g) (koszulComplex A n a) (kFlat_koszulComplex A n a)
    (acyclic_koszulComplex A n a)

end Stacks.AlgebraicGeometry.ProjKoszulOverBase

end
