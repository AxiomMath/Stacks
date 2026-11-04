module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic

/-!
# Proper support of a finite type quasi-coherent module

Let `f : X ⟶ S` be a morphism of schemes which is locally of finite type and let `F` be a
quasi-coherent `O_X`-module of finite type. The support of `F` is a closed subset of `X`, so it
makes sense to ask that it be proper over `S` in the sense of
`AlgebraicGeometry.IsProperOver`. This file shows that this holds exactly when the
scheme-theoretic support of `F` is proper over `S`, and exactly when `F` is the direct image of
a quasi-coherent module of finite type on *some* closed subscheme of `X` proper over `S`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isProperOver_supp_iff_isProper_schemeTheoreticSupport`:
  the support of `F` is proper over `S` if and only if its scheme-theoretic support is.
* `AlgebraicGeometry.Scheme.Modules.isProper_schemeTheoreticSupport_iff_exists_pushforward`:
  the scheme-theoretic support of `F` is proper over `S` if and only if `F` is the direct image
  of a quasi-coherent module of finite type on a closed subscheme of `X` proper over `S`.

## Implementation notes

The two results are the two halves of the three-way equivalence of [Stacks, Tag 0CYS]: the
first is conditions (1) and (2), the second is conditions (2) and (3).

Condition (1) speaks about the reduced induced structure on the support, condition (2) about the
scheme-theoretic support. These are two closed subscheme structures on the same closed subset,
by `AlgebraicGeometry.Scheme.Modules.supp_eq_support_schemeTheoreticSupport`, so the comparison
of closed subscheme structures from [Stacks, Tag 0CYL] identifies the two conditions. For
condition (3) the forward implication is the existence of a descent of `F` to its
scheme-theoretic support, and the converse uses minimality of the scheme-theoretic support
together with the fact that a closed subset of a proper closed subset is proper
([Stacks, Tag 0CYN]).

Equality `(Z → X)_* G = F` of the source is expressed as `Nonempty (… ≅ F)`, an isomorphism of
`O_X`-modules without a chosen name, since equality of objects of the category of modules is
not the right notion.

## References

* [Stacks Project, Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
  (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- The support of a quasi-coherent module of finite type is proper over the base if and only if
its scheme-theoretic support is proper over the base. -/
@[stacks 0CYS "conditions (1) and (2)"]
public theorem isProperOver_supp_iff_isProper_schemeTheoreticSupport :
    IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩ ↔
      IsProper ((schemeTheoreticSupport F).subschemeι ≫ f) := by
  have hsupp : (schemeTheoreticSupport F).support =
      (⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩ : Closeds X) :=
    Closeds.ext (supp_eq_support_schemeTheoreticSupport F).symm
  exact ⟨fun h ↦ (exists_isProper_iff_forall_isProper f _).1
      ((isProperOver_iff_exists_isProper f _).1 h) _ hsupp,
    fun h ↦ (isProperOver_iff_exists_isProper f _).2 ⟨_, hsupp, h⟩⟩

/-- The scheme-theoretic support of a quasi-coherent module `F` of finite type is proper over the
base if and only if there is a closed subscheme of `X` proper over the base carrying a
quasi-coherent module of finite type whose direct image is `F`. -/
@[stacks 0CYS "conditions (2) and (3)"]
public theorem isProper_schemeTheoreticSupport_iff_exists_pushforward :
    IsProper ((schemeTheoreticSupport F).subschemeι ≫ f) ↔
      ∃ (J : X.IdealSheafData) (G : J.subscheme.Modules),
        G.IsFiniteType ∧ G.IsQuasicoherent ∧ IsProper (J.subschemeι ≫ f) ∧
          Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj G ≅ F) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨G, hGqc, hGft, hGiso⟩ := exists_module_on_schemeTheoreticSupport F
    exact ⟨schemeTheoreticSupport F, G, hGft, hGqc, h, hGiso⟩
  · rintro ⟨J, G, -, -, hJ, ⟨e⟩⟩
    have hle : (schemeTheoreticSupport F).support ≤ J.support :=
      Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.2 <| by
        rw [Scheme.IdealSheafData.vanishingIdeal_support]
        exact (schemeTheoreticSupport_isSmallest F J G e).trans
          (Scheme.IdealSheafData.le_radical _)
    have hp : IsProperOver f (schemeTheoreticSupport F).support :=
      isProperOver_of_le f hle ((isProperOver_iff_exists_isProper f J.support).2 ⟨J, rfl, hJ⟩)
    exact (exists_isProper_iff_forall_isProper f _).1
      ((isProperOver_iff_exists_isProper f _).1 hp) _ rfl

end AlgebraicGeometry.Scheme.Modules

end
