module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CanonicalTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistQuasiCoherentDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.DerivedCategory.IsZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical twist of `ℙⁿ_R` in the derived category

Let `R` be a commutative ring, `n ≥ 0` and `X = ℙⁿ_R = Proj R[T₀, …, Tₙ]`, and let
`π : X ⟶ Spec R` be the structure morphism. This file reads the two consequences of Serre's
computation collected in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/CanonicalTwist.lean` — the trace
isomorphism `Hⁿ(X, 𝒪(-n-1)) ≅ R` with the concentration of that cohomology in degree `n`, and the
total acyclicity of `𝒪(-1), …, 𝒪(-n)` — as statements about `RΓ(X, -) : D(𝒪_X) ⥤ D(R)` applied to
the `D_QCoh` objects of `Stacks.ProjectiveSpace.Cohomology.twistQcoh`.

Two of the three statements below are strictly stronger than their input, because they also cover
the degrees `q < 0`, which Serre's computation — indexed by `q : ℕ` — says nothing about. There
the vanishing is left t-exactness of an unbounded right derived functor,
`Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj`: a module placed in cohomological
degree zero is bounded below by zero, hence so is `RΓ` of it. So the acyclicity statement is an
assertion about the *object* `RΓ(X, 𝒪(d))` of `D(R)` and not only about its cohomology modules.

These are the inputs that the Stacks project's computation of the twisted inverse image on
projective space, [Stacks, Tag 0A9W], takes from the cohomology of projective space: there the
trace isomorphism is what produces the map `Rf_*(f^*ℒ(-n-1)[n]) → 𝒪_Y` from which the asserted
isomorphism `c : f^*ℒ(-n-1)[n] → a(𝒪_Y)` is obtained by adjunction, and the acyclicity is what
makes the comparison vacuous on the remaining generators `𝒪_X(-1), …, 𝒪_X(-n)` of
[Stacks, Tag 0A9V].

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.derivedGlobalSectionsTwistQcohCanonicalIso` — **the trace
  isomorphism in the derived category**: `Hⁿ(RΓ(X, 𝒪(-n-1))) ≅ R`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.isZero_homology_derivedGlobalSections_twistQcoh_of_neg` —
  `H^q(RΓ(X, 𝒪(d))) = 0` for every `q < 0` and every `d`.
* `Stacks.ProjectiveSpace.Cohomology.isZero_homology_derivedGlobalSections_twistQcoh_canonical` —
  **`H^q(RΓ(X, 𝒪(-n-1))) = 0` for every `q : ℤ` with `q ≠ n`**, so `RΓ(X, 𝒪(-n-1))` is
  concentrated in degree `n`, where the trace isomorphism identifies it with `R`.
* `Stacks.ProjectiveSpace.Cohomology.isZero_derivedGlobalSections_twistQcoh_of_neg_le` —
  **`RΓ(X, 𝒪(d)) = 0` in `D(R)` when `-n ≤ d < 0`**: the twists strictly between `𝒪(-n-1)` and
  `𝒪` have no derived global sections at all.

## Implementation notes

The derived-category model is the locally small one, as in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/TwistQuasiCoherentDerived.lean`; see the
implementation notes there for why, and for why no isomorphism is transported between models.

`Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj` is stated for
`Stacks.DerivedFunctor.totalRightDerived`, which is the same functor as
`AlgebraicGeometry.derivedGlobalSectionsOver`: both are the total right derived functor of the
degreewise functor on the homotopy category of cochain complexes, and both spellings are
`abbrev`s of that. The bound `0` it is applied at comes from the instance
`Stacks.ProjectiveSpace.Cohomology.isGE_twistQcoh_obj`, which has to be stated because
`Stacks.ProjectiveSpace.Cohomology.twistQcoh` is a `def`: instance search will not unfold it to
see the single complex underneath.

No `@[stacks]` attribute is attached. Each statement is one value or one range of the twist in
Serre's computation, whose covering set is registered on the declarations named in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/CanonicalTwist.lean`, moved to the
model of the derived category in which the duality machinery is written. Nothing here is a new
reading of a source result.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

/-- **A sheaf of modules placed in cohomological degree zero has no cohomology below degree
zero.** This is Mathlib's instance for the single functors of the canonical t-structure, named so
that it can be applied at a *concrete* scheme: at `X = Proj R[T₀, …, Tₙ]` instance search does not
find it, and the application of this lemma does. -/
theorem isGE_singleFunctor_obj (X : Scheme.{u}) (M : X.Modules) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj M).IsGE 0 :=
  inferInstance

/-- `𝒪_X(d)` placed in cohomological degree zero has no cohomology below degree zero. This is
needed as a declaration rather than found by instance search because
`Stacks.ProjectiveSpace.Cohomology.twistQcoh` is a `def`. -/
instance isGE_twistQcoh_obj : (twistQcoh R n d).obj.IsGE 0 :=
  isGE_singleFunctor_obj _ _

/-! ### Vanishing below degree zero -/

/-- **`RΓ(X, 𝒪(d))` has no cohomology in negative degrees**, for every twist `d`: the twisting
sheaf sits in cohomological degree zero, and the unbounded right derived functor of an additive
functor is left t-exact. -/
theorem isZero_homology_derivedGlobalSections_twistQcoh_of_neg (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
      ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
        (twistQcoh R n d).obj)) :=
  Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
    (AlgebraicGeometry.globalSectionsOver (projToSpecCoeff R n)) (twistQcoh R n d).obj 0 q hq

/-! ### The canonical twist: concentration and the trace isomorphism -/

/-- To show `H^q(RΓ(X, 𝒪(d))) = 0` it suffices to treat the degrees `q = m` with `m : ℕ`. -/
private theorem isZero_homology_derivedGlobalSections_twistQcoh_of_nat (q : ℤ)
    (h : ∀ m : ℕ, q = m → IsZero (twistCohomology R n d m)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
      ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
        (twistQcoh R n d).obj)) := by
  rcases lt_or_ge q 0 with hq | hq
  · exact isZero_homology_derivedGlobalSections_twistQcoh_of_neg R n d q hq
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = (m : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg hq).symm⟩
    exact (twistCohomologyIsoDerivedGlobalSections R n d m).isZero_iff.1 (h m rfl)

/-- **`RΓ(X, 𝒪(-n-1))` is concentrated in degree `n`**: its cohomology vanishes in every other
degree, negative degrees included. In degrees `q ≥ 0` this is
`Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_canonical`, the top-degree row of
[Stacks, Tag 01XT] at `d = -n-1`, moved across
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoDerivedGlobalSections`. -/
@[ega "III 2.1.12" "(i), special case"]
theorem isZero_homology_derivedGlobalSections_twistQcoh_canonical (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
      ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
        (twistQcoh R n (-(n : ℤ) - 1)).obj)) := by
  exact isZero_homology_derivedGlobalSections_twistQcoh_of_nat R n _ q fun m hm =>
    isZero_twistCohomology_canonical R n m (by omega)

/-- **The trace isomorphism in the derived category**: `Hⁿ(RΓ(ℙⁿ_R, 𝒪(-n-1))) ≅ R`. Together with
`Stacks.ProjectiveSpace.Cohomology.isZero_homology_derivedGlobalSections_twistQcoh_canonical` this
says that `RΓ(X, 𝒪(-n-1))[n]` has the single cohomology module `R` in degree zero, which is the
map `Rf_*(f^*ℒ(-n-1)[n]) → 𝒪_Y` that [Stacks, Tag 0A9W] obtains from
Cohomology of Schemes, Lemma 30.8.4. -/
def derivedGlobalSectionsTwistQcohCanonicalIso :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
        ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
          (twistQcoh R n (-(n : ℤ) - 1)).obj) ≅
      ModuleCat.of R R :=
  (twistCohomologyIsoDerivedGlobalSections R n (-(n : ℤ) - 1) n).symm ≪≫
    twistCohomologyCanonicalIsoCoeff R n

/-- **`RΓ(ℙⁿ_R, 𝒪(-n-1)) ≅ R[-n]` in `D(R)`**, equivalently `RΓ(X, 𝒪(-n-1))[n] ≅ R`: the derived
global sections of the canonical twist are the coefficient ring placed in cohomological degree
`n`. The isomorphism is noncanonical, as in the source.

Its cohomology is concentrated in degree `n`, so it is isomorphic to *some* module placed in
degree `n`; that module is its degree-`n` cohomology, which the trace isomorphism
`Stacks.ProjectiveSpace.Cohomology.derivedGlobalSectionsTwistQcohCanonicalIso` identifies
with `R`. For the structure morphism `π : ℙⁿ_R ⟶ Spec R` this is the statement
`Rπ_*𝒪(-n-1)[n] ≅ 𝒪` from which [Stacks, Tag 0A9W] produces its comparison map by
adjunction. -/
theorem nonempty_derivedGlobalSections_twistQcoh_canonical_iso_single :
    Nonempty ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
          (twistQcoh R n (-(n : ℤ) - 1)).obj ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)) := by
  have : ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
      (twistQcoh R n (-(n : ℤ) - 1)).obj).IsGE (n : ℤ) :=
    (DerivedCategory.isGE_iff _ _).2 fun i hi =>
      isZero_homology_derivedGlobalSections_twistQcoh_canonical R n i (by omega)
  have : ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
      (twistQcoh R n (-(n : ℤ) - 1)).obj).IsLE (n : ℤ) :=
    (DerivedCategory.isLE_iff _ _).2 fun i hi =>
      isZero_homology_derivedGlobalSections_twistQcoh_canonical R n i (by omega)
  obtain ⟨Y, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
        (twistQcoh R n (-(n : ℤ) - 1)).obj) (n : ℤ)
  refine ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} R) (n : ℤ)).app Y).symm ≪≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).mapIso e).symm ≪≫
        derivedGlobalSectionsTwistQcohCanonicalIso R n)⟩

/-! ### Total acyclicity of the twists between `𝒪(-n-1)` and `𝒪` -/

/-- **`RΓ(ℙⁿ_R, 𝒪(d)) = 0` in `D(R)` when `-n ≤ d < 0`**: the twists `𝒪(-1), …, 𝒪(-n)` have no
derived global sections at all. An object of the unbounded derived category is zero exactly when
all of its cohomology vanishes; in degrees `q ≥ 0` that is
`Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_neg_le` and in negative degrees it is
left t-exactness. -/
theorem isZero_derivedGlobalSections_twistQcoh_of_neg_le
    (hd₁ : -(n : ℤ) ≤ d) (hd₂ : d < 0) :
    IsZero ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
      (twistQcoh R n d).obj) := by
  refine (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun q => ?_
  exact isZero_homology_derivedGlobalSections_twistQcoh_of_nat R n d q fun m _ =>
    isZero_twistCohomology_of_neg_le R n d hd₁ hd₂ m

end Stacks.ProjectiveSpace.Cohomology

end
