module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction

/-!
# Scheme structures on a closed subset, and the reduced induced one

Let `X` be a scheme and let `Z ⊆ X` be a closed subset. A *scheme structure on `Z`* is a closed
subscheme of `X` whose underlying set is `Z`, recorded by its ideal sheaf; the *reduced induced
scheme structure* on `Z` is the one cut out by the vanishing ideal sheaf of `Z`, and it is the
unique reduced one. The reduction `X_red` of `X` is the reduced induced scheme structure on `X`
itself.

## Main definitions

* `AlgebraicGeometry.Scheme.SchemeStructure`: a scheme structure on a closed subset `Z` of `X`.
* `AlgebraicGeometry.Scheme.SchemeStructure.toScheme` and
  `AlgebraicGeometry.Scheme.SchemeStructure.ι`: the closed subscheme it is, and its closed
  immersion into `X`.
* `AlgebraicGeometry.Scheme.reducedInduced`: the reduced induced scheme structure on `Z`.

## Main results

* `AlgebraicGeometry.Scheme.SchemeStructure.range_ι`: the underlying set of a scheme structure on
  `Z` is `Z`.
* `AlgebraicGeometry.Scheme.exists_schemeStructure_of_isClosedImmersion`: every closed immersion
  into `X` with image `Z` is, up to isomorphism over `X`, the closed immersion of a scheme
  structure on `Z`.
* `AlgebraicGeometry.Scheme.SchemeStructure.eq_reducedInduced`: a reduced scheme structure on `Z`
  is the reduced induced one.
* `AlgebraicGeometry.Scheme.reduction_eq_reducedInduced_top`: the reduction of `X` is the reduced
  induced scheme structure on all of `X`.

## References

* [Stacks Project, Tag 01J4](https://stacks.math.columbia.edu/tag/01J4)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A **scheme structure** on a closed subset `Z` of a scheme `X`: a closed subscheme of `X`
whose underlying set is `Z`, recorded by an ideal sheaf `ideal` on `X` whose support is `Z`. -/
@[ega "I 4.1.3"]
structure SchemeStructure (X : Scheme.{u}) (Z : Closeds X) where
  /-- The ideal sheaf cutting out the closed subscheme. -/
  ideal : X.IdealSheafData
  /-- The underlying closed subset of the closed subscheme is `Z`. -/
  support_eq : ideal.support = Z

add_to_stacks 01J4 "scheme structure on Z" AlgebraicGeometry.Scheme.SchemeStructure

namespace SchemeStructure

variable {X : Scheme.{u}} {Z : Closeds X} (S : X.SchemeStructure Z)

/-- Two scheme structures on `Z` with the same ideal sheaf are equal. -/
@[ext]
theorem ext {S T : X.SchemeStructure Z} (h : S.ideal = T.ideal) : S = T := by
  cases S; cases T; subst h; rfl

/-- The closed subscheme of `X` underlying a scheme structure on `Z`. -/
noncomputable def toScheme : Scheme.{u} :=
  S.ideal.subscheme

/-- The closed immersion into `X` of the closed subscheme underlying a scheme structure
on `Z`. -/
noncomputable def ι : S.toScheme ⟶ X :=
  S.ideal.subschemeι

/-- The morphism `ι` of a scheme structure is a closed immersion. -/
instance isClosedImmersion_ι : IsClosedImmersion S.ι :=
  inferInstanceAs (IsClosedImmersion S.ideal.subschemeι)

/-- **The underlying set of a scheme structure on `Z` is `Z`.** -/
@[simp]
theorem range_ι : Set.range S.ι = (Z : Set X) := by
  show Set.range S.ideal.subschemeι = (Z : Set X)
  rw [IdealSheafData.range_subschemeι, S.support_eq]

end SchemeStructure

/-- **Every closed immersion into `X` with image `Z` is a scheme structure on `Z`.** Given a
closed immersion `i : W ⟶ X` whose set-theoretic image is `Z`, there is a scheme structure `S` on
`Z` and an isomorphism `W ≅ S.toScheme` over `X`. -/
theorem exists_schemeStructure_of_isClosedImmersion {X W : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] {Z : Closeds X} (hZ : Set.range i = (Z : Set X)) :
    ∃ (S : X.SchemeStructure Z) (e : W ≅ S.toScheme), e.hom ≫ S.ι = i := by
  let S : X.SchemeStructure Z :=
    ⟨i.ker, Closeds.ext (by rw [Scheme.Hom.support_ker, hZ, Z.isClosed.closure_eq])⟩
  have hker : S.ι.ker = i.ker := IdealSheafData.ker_subschemeι S.ideal
  have : IsIso (IsClosedImmersion.lift S.ι i hker.le) := IsClosedImmersion.isIso_lift S.ι i hker
  exact ⟨S, asIso (IsClosedImmersion.lift S.ι i hker.le),
    IsClosedImmersion.lift_fac S.ι i hker.le⟩

/-- **The reduced induced scheme structure on a closed subset `Z` of `X`:** the closed subscheme
cut out by the vanishing ideal sheaf of `Z`. -/
@[stacks 01J4 "the reduced induced scheme structure on Z", ega "I 5.5.4", ega "IV 4.9.4"]
noncomputable def reducedInduced {X : Scheme.{u}} (Z : Closeds X) : X.SchemeStructure Z :=
  ⟨IdealSheafData.vanishingIdeal Z, Closeds.ext (IdealSheafData.coe_support_vanishingIdeal Z)⟩

/-- The reduced induced scheme structure is reduced. -/
instance isReduced_reducedInduced {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (reducedInduced Z).toScheme :=
  inferInstanceAs (IsReduced (IdealSheafData.vanishingIdeal Z).subscheme)

/-- **A reduced scheme structure on `Z` is the reduced induced one.** -/
theorem SchemeStructure.eq_reducedInduced {X : Scheme.{u}} {Z : Closeds X}
    (S : X.SchemeStructure Z) [IsReduced S.toScheme] : S = reducedInduced Z := by
  have : IsReduced S.ideal.subscheme := inferInstanceAs (IsReduced S.toScheme)
  exact SchemeStructure.ext
    (IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme S.ideal Z S.support_eq)

/-- **The reduction `X_red` of `X` is the reduced induced scheme structure on all of `X`.** -/
@[ega "I 5.1.3" "partial"]
theorem reduction_eq_reducedInduced_top (X : Scheme.{u}) :
    X.reduction = (reducedInduced (⊤ : Closeds X)).toScheme := by
  show X.nilradical.subscheme = (IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme
  rw [IdealSheafData.vanishingIdeal_top]

end AlgebraicGeometry.Scheme

end
