module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.RingTheory.Nagata.Examples
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# A scheme of finite type over a field is a Japanese scheme

An integral scheme locally of finite type over a field is Japanese in the sense of
[Stacks, Tag 033S]:  every point has an affine open neighbourhood whose ring of sections is an
N-2 domain.  This is the hypothesis of `AlgebraicGeometry.normalization_isFinite`
([Stacks, Tag 035R]), so it is what makes the normalization of a variety a finite morphism.

## Main definitions

* `Stacks.AlgebraicGeometry.UnitsNormalProper.structMapLE`:  the structural ring map
  `k →+* Γ(X, U)` of a scheme `X` over `Spec k` and an open `U`.

## Main results

* `Stacks.AlgebraicGeometry.UnitsNormalProper.isJapaneseRing_of_finiteType_field`:  a domain of
  finite type over a field is N-2.
* `Stacks.AlgebraicGeometry.UnitsNormalProper.finiteType_structMapLE`:  the ring of sections on
  an affine open of a scheme locally of finite type over `Spec k` is a finite-type `k`-algebra.
* `Stacks.AlgebraicGeometry.UnitsNormalProper.isJapaneseScheme_of_locallyOfFiniteType`:  the
  scheme-level conclusion.

## References

* [Stacks Project, Tag 033S](https://stacks.math.columbia.edu/tag/033S)
* [Stacks Project, Tag 0334](https://stacks.math.columbia.edu/tag/0334)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.UnitsNormalProper

/-- A domain of finite type over a field is N-2 (Japanese). -/
theorem isJapaneseRing_of_finiteType_field (k : Type u) [Field k] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] : IsJapaneseRing A := by
  have h12 : IsNagataRing k →
      ∀ (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S], IsNagataRing S :=
    ((isNagataRing_tfae (R := k)).out 1 2).mp
  have hN : IsNagataRing A := h12 IsNagataRing.of_field A
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  exact IsJapaneseRing.of_ringEquiv (RingEquiv.quotientBot A) (hN.isJapaneseRing_quotient ⊥)

/-- The structural ring map `k →+* Γ(X, U)` attached to a scheme over `Spec k` and an open `U`. -/
noncomputable def structMapLE {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (U : X.Opens) : k →+* Γ(X, U) :=
  (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- For a morphism `f : X ⟶ Spec k` locally of finite type and an affine open `U` of `X`, the
structural ring map `k →+* Γ(X, U)` is of finite type. -/
theorem finiteType_structMapLE {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (U : X.affineOpens) : (structMapLE f U.1).FiniteType := by
  refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
  · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType)
      f ‹LocallyOfFiniteType f› ⟨⊤, isAffineOpen_top _⟩ U _
  · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2

/-- A scheme of finite type over a field whose underlying space is integral is Japanese. -/
theorem isJapaneseScheme_of_locallyOfFiniteType (k : Type u) [Field k] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : IsJapaneseScheme X := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := x) (U := ⊤) trivial
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  have : Nonempty (U : Type u) := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U) := AlgebraicGeometry.IsIntegral.component_integral U
  let _ : Algebra k Γ(X, U) := (structMapLE f U).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := finiteType_structMapLE f ⟨U, hU⟩
  exact isJapaneseRing_of_finiteType_field k Γ(X, U)

end Stacks.AlgebraicGeometry.UnitsNormalProper
