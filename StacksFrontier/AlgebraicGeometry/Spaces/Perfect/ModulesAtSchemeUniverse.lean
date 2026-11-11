module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# Modules on the small étale site of an algebraic space at the universe of the schemes

Let `X` be an algebraic space over a scheme `S`.  This file pins by hand the abelian structure of
the `𝒪_X`-modules with sections in the universe of the schemes and the standard model of
`D(𝒪_X)` at that universe, and records two elementary facts about them that are used in files
whose import closure contains the locally small models of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModulesAbelianAtSchemeUniverse` and
  `AlgebraicGeometry.Space.smallEtaleModulesHasDerivedCategory`: the pinned instances.
* `AlgebraicGeometry.Space.supportOfSheaf_eq_of_sheafIso`: isomorphic abelian sheaves on the small
  étale site have the same support (from Stacks 04KB).
* `AlgebraicGeometry.Space.isPseudoCoherentComplexFrom_of_le` and
  `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_le`: pseudo-coherence from a degree
  (Stacks 08FT) is monotone in that degree.

## Implementation notes

The module sections are at the universe of the schemes, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationElementarySquare.lean`: at that
universe every sheafification and local-bijectivity hypothesis that
`AlgebraicGeometry.RingedSite.IsPerfect`, `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom`
and `AlgebraicGeometry.Space.ApproximationHolds` ask of the small étale site and of its slices
is an instance, by `AlgebraicGeometry.Space.RingedSite`, so none appears as a binder.

The standard model is selected at raised priority, as in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/Affine.lean`: a plain
`attribute [local instance]` is not enough in a file with `AlgebraicGeometry.derivedTilde` in
its import closure.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-! ### Instances pinned by hand -/

/-- The abelian structure of the `𝒪_X`-modules with sections in the universe of the schemes,
written out instead of being found by instance search.

It is the term instance search returns, namely `SheafOfModules.instAbelian` fed the two
sheafification instances of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, so nothing is
changed by using it.  The search itself is unusable in a file importing
`StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine`, which Stacks
08EQ brings in: it declares sheafification instances for every universe of module sections
containing the objects of the site, whose universe parameter occurs only inside a `max`, so
matching them against a goal at the universe of the schemes leaves an unsolvable universe
constraint postponed rather than failing, and the postponed constraint is reported as an error.
This is the device of `AlgebraicGeometry.Space.smallEtaleModulesAbelian` in
`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedInjective.lean`, for the same reason. -/
@[instance_reducible] noncomputable def smallEtaleModulesAbelianAtSchemeUniverse :
    Abelian (Modules.{u, u} B S hS X hX) :=
  @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X hX)
    (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X hX)

attribute [local instance 10000] smallEtaleModulesAbelianAtSchemeUniverse in
/-- The standard model of `D(𝒪_X)` at the universe of the schemes, written out instead of being
found by instance search, for the reason recorded on
`AlgebraicGeometry.Space.smallEtaleModulesAbelianAtSchemeUniverse`.  Here the offending candidates
are the locally small models of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which
Stacks 08EQ brings in through `AlgebraicGeometry.derivedTilde`: their universe of
morphisms is a `max` over the universe of the objects of the site, which for the small étale
site is `u + 1`, so matching them against the module universe `u` leaves the same unsolvable
constraint postponed.  This is `CategoryTheory.HasDerivedCategory.standard` fed the abelian
structure above, which is the term
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/Approximation.lean` selects, so the objects of
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` live in this model. -/
@[instance_reducible] noncomputable def smallEtaleModulesHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X hX) :=
  @HasDerivedCategory.standard (Modules.{u, u} B S hS X hX) _
    (smallEtaleModulesAbelianAtSchemeUniverse B S hS X hX)

/-! ### Support is an invariant of an abelian sheaf on the small étale site -/

attribute [local instance 10000] smallEtaleModulesAbelianAtSchemeUniverse
  smallEtaleModulesHasDerivedCategory in
include hX in
/-- Isomorphic abelian sheaves on the small étale site of an algebraic space have the same
support: an isomorphism is a monomorphism both ways, so Stacks 04KB applies twice. -/
theorem supportOfSheaf_eq_of_sheafIso
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u}} (e : F ≅ G) :
    supportOfSheaf B S hS X F = supportOfSheaf B S hS X G :=
  -- instance search for `Mono e.hom` times out under Lean v4.35.0
  have := IsIso.mono_of_iso e.hom
  have := IsIso.mono_of_iso e.inv
  Set.eq_of_subset_of_subset (supportOfSheaf_subset_of_mono B S hS X hX e.hom)
    (supportOfSheaf_subset_of_mono B S hS X hX e.inv)

/-! ### Pseudo-coherence from a degree is monotone in that degree -/

attribute [local instance 10000] smallEtaleModulesAbelianAtSchemeUniverse
  smallEtaleModulesHasDerivedCategory in
/-- **Monotonicity of Stacks 08FT part (1) in its degree.** A complex of `𝒪_X`-modules which is
`a`-pseudo-coherent is `b`-pseudo-coherent for every `b ≥ a`: the local approximations are the
same ones, their isomorphism range `> a` contains `> b`, and in degree `b` either `b = a`, where
the surjection is the given one, or `b > a`, where the given isomorphism is one. -/
theorem isPseudoCoherentComplexFrom_of_le
    (K : CochainComplex (Modules.{u, u} B S hS X hX) ℤ) {a b : ℤ}
    (h : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentComplexFrom K a) (hab : a ≤ b) :
    (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentComplexFrom K b := by
  intro U
  obtain ⟨T, hT, hmem⟩ := h U
  refine ⟨T, hT, fun {V} g hg => ?_⟩
  obtain ⟨P, hP, α, hiso, hepi⟩ := hmem g hg
  refine ⟨P, hP, α, fun j hj => hiso j (lt_of_le_of_lt hab hj), ?_⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact hepi
  · have := hiso b hlt
    infer_instance

attribute [local instance 10000] smallEtaleModulesAbelianAtSchemeUniverse
  smallEtaleModulesHasDerivedCategory in
/-- **Monotonicity of Stacks 08FT part (3) in its degree**, for an object of `D(𝒪_X)`: the
representing complex of `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` is monotone in the
degree by `AlgebraicGeometry.Space.isPseudoCoherentComplexFrom_of_le`. -/
theorem isPseudoCoherentFrom_of_le {E : DerivedCategory (Modules.{u, u} B S hS X hX)} {a b : ℤ}
    (h : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E a) (hab : a ≤ b) :
    (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E b := by
  obtain ⟨K, hK, he⟩ := h
  exact ⟨K, isPseudoCoherentComplexFrom_of_le B S hS X hX K hK hab, he⟩

end AlgebraicGeometry.Space

end
