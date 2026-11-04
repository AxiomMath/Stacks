module

public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# Morphisms out of a perfect complex into a complex with countable cohomology

Let `R` be a ring and let `M` be an object of `D(R)` whose cohomology modules `H^i(M)` all have
countable underlying sets. Then for every perfect object `P` of `D(R)` and every integer `n` the
group `Hom_{D(R)}(P, M[n])` is countable.

This is the module-level input of the affine case of [Stacks, Tag 0CRP]: there `P` is a finite
complex of finite projective modules representing a perfect complex on an affine scheme, and
`M` represents the restriction of `K`.

## Main definitions

* `StacksDraft.Perfect.countableHomInto M`: the objects `P` of `D(R)` such that every
  `Hom(P, M[n])` is countable.

## Main results

* `StacksDraft.Perfect.countable_hom_shift_of_isPerfect`: for `P` perfect and `M` with countable
  cohomology, every `Hom(P, M[n])` is countable.

## Implementation notes

The source argues by induction on the length of a finite complex of finite projective modules
representing `P`. The same induction is packaged here by [Stacks, Tag 0ATI]: the perfect objects
are the smallest strictly full, saturated, triangulated subcategory of `D(R)` containing `R[0]`
(`StacksDraft.Perfect.isPerfect_eq_triangEnvelope_singleton_regularModule`). So it suffices that
`StacksDraft.Perfect.countableHomInto M` is closed under isomorphisms, shifts, extensions and
retracts — each of which is a statement about Hom groups — and that it contains `R[0]`, which is
the corepresentability `Hom(R[0], M[n]) = H^0(M[n]) = H^n(M)` of
`DerivedCategory.homologyFromSingleAddEquiv`.

The derived category is the standard one, as in [Stacks, Tag 0ATI].

## References

* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP)
* [Stacks Project, Tag 0ATI](https://stacks.math.columbia.edu/tag/0ATI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

variable {R : Type u} [Ring R]

/-- The objects `P` of `D(R)` such that `Hom(P, M[n])` is countable for every `n`. -/
def countableHomInto (M : DerivedCategory (ModuleCat.{u} R)) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun P => ∀ n : ℤ, Countable (P ⟶ M⟦n⟧)

variable (M : DerivedCategory (ModuleCat.{u} R))

/-- `countableHomInto M` is closed under isomorphisms. -/
instance countableHomInto_isClosedUnderIsomorphisms :
    (countableHomInto M).IsClosedUnderIsomorphisms where
  of_iso e h n :=
    have := h n
    Function.Injective.countable (f := fun g => e.hom ≫ g)
      (fun _ _ hg => by simpa using congrArg (e.inv ≫ ·) hg)

/-- `countableHomInto M` contains a zero object. -/
instance countableHomInto_containsZero : (countableHomInto M).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun n =>
    have : Subsingleton ((0 : DerivedCategory (ModuleCat.{u} R)) ⟶ M⟦n⟧) :=
      ⟨fun _ _ => (isZero_zero _).eq_of_src _ _⟩
    inferInstance⟩

/-- `countableHomInto M` is stable under every shift `[a]`, `a : ℤ`. -/
instance countableHomInto_isStableUnderShift :
    (countableHomInto M).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun P hP n => by
    have := hP (n + -a)
    let e : M⟦n⟧⟦-a⟧ ≅ M⟦n + -a⟧ := (shiftFunctorAdd' _ n (-a) (n + -a) rfl).symm.app M
    exact Function.Injective.countable
      (f := fun g : P⟦a⟧ ⟶ M⟦n⟧ =>
        ((shiftEquiv (DerivedCategory (ModuleCat.{u} R)) a).toAdjunction.homEquiv P (M⟦n⟧) g) ≫
          e.hom)
      (fun _ _ hg => (Adjunction.homEquiv _ _ _).injective ((cancel_mono e.hom).1 hg))⟩

/-- `countableHomInto M` is closed under extensions: in a distinguished triangle
`P₁ ⟶ P₂ ⟶ P₃ ⟶ P₁[1]` with `P₁` and `P₃` in `countableHomInto M`, so is `P₂`. -/
instance countableHomInto_isTriangulatedClosed₂ :
    (countableHomInto M).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ n => by
    classical
    have := h₁ n
    have := h₃ n
    let φ : (T.obj₂ ⟶ M⟦n⟧) → (T.obj₁ ⟶ M⟦n⟧) := fun f => T.mor₁ ≫ f
    let s : Set.range φ → (T.obj₂ ⟶ M⟦n⟧) := fun x => x.2.choose
    have hs : ∀ x, φ (s x) = x.1 := fun x => x.2.choose_spec
    refine Function.Surjective.countable
      (f := fun p : Set.range φ × (T.obj₃ ⟶ M⟦n⟧) => s p.1 + T.mor₂ ≫ p.2) ?_
    intro f
    have hzero : T.mor₁ ≫ (f - s ⟨φ f, Set.mem_range_self f⟩) = 0 := by
      rw [Preadditive.comp_sub]
      exact sub_eq_zero.2 (hs ⟨φ f, Set.mem_range_self f⟩).symm
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT _ hzero
    refine ⟨(⟨φ f, Set.mem_range_self f⟩, g), ?_⟩
    change s _ + T.mor₂ ≫ g = f
    rw [← hg]
    abel

/-- `countableHomInto M` is a triangulated subcategory of `D(R)`. -/
instance countableHomInto_isTriangulated : (countableHomInto M).IsTriangulated where

/-- `countableHomInto M` is stable under retracts. -/
instance countableHomInto_isStableUnderRetracts :
    (countableHomInto M).IsStableUnderRetracts where
  of_retract r h n :=
    have := h n
    Function.Injective.countable (f := fun g => r.r ≫ g)
      (fun _ _ hg => by simpa using congrArg (r.i ≫ ·) hg)

/-- If every cohomology module `H^i(M)` is countable, then `R[0]` lies in `countableHomInto M`,
that is, every `Hom(R[0], M[n])` is countable. -/
theorem countableHomInto_regularModule (hM : ∀ i : ℤ,
      Countable ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    countableHomInto M
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) := by
  intro n
  have : Projective (ModuleCat.of R R) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R R)
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj (M⟦n⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso n 0 n (by simp)).app M
  have := hM n
  exact Function.Injective.countable
    (f := fun g => ((DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of R R) (M⟦n⟧) 0 g)
      ≫ e.hom).hom (1 : R))
    (fun _ _ hg =>
      (DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of R R) (M⟦n⟧) 0).injective
        ((cancel_mono e.hom).1 (ModuleCat.hom_ext (LinearMap.ext_ring hg))))

/-- **Morphisms out of a perfect complex into a complex with countable cohomology.** If every
cohomology module of `M` is countable, then `Hom_{D(R)}(P, M[n])` is countable for every perfect
object `P` of `D(R)` and every `n`. -/
theorem countable_hom_shift_of_isPerfect (hM : ∀ i : ℤ,
      Countable ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M))
    (P : DerivedCategory (ModuleCat.{u} R)) (hP : IsPerfect P) (n : ℤ) :
    Countable (P ⟶ M⟦n⟧) := by
  rw [show (IsPerfect : ObjectProperty _) P ↔ _ from
    iff_of_eq (congrFun isPerfect_eq_triangEnvelope_singleton_regularModule P)] at hP
  refine ((ObjectProperty.triangEnvelope_le_iff (Q := countableHomInto M) _).2 ?_) P hP n
  intro Q hQ
  obtain rfl : _ = Q := by simpa only [ObjectProperty.singleton_iff] using hQ
  exact countableHomInto_regularModule M hM

end StacksDraft.Perfect

end
