module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.Final.Type

/-!
# Comparing two colimit presentations of a commutative ring

A commutative ring presented as a filtered colimit of a diagram of commutative rings is
determined by that presentation up to a unique ring isomorphism compatible with the colimit
injections. This file provides the comparison in the form in which it is used: both
presentations are given as cocones *of types* which are colimits, together with the fact that
each injection is a ring homomorphism, and the conclusion is a ring equivalence commuting with
the injections.

Two auxiliary facts about colimits of types are proved on the way, both of which are about an
index category that is too large for the ambient universe to see directly.

## Main definitions

* `CommRingCat.coconeTypesOfRingHoms` reads a compatible family of ring homomorphisms out of a
  diagram of commutative rings as a cocone of types.  The target is only required to be a
  non-associative semiring, so that the comparison applies to the carrier of an object of
  `RingCat` which has not been given a commutative ring structure.
* `CommRingCat.ringEquivOfIsColimit` is the comparison ring equivalence between two colimit
  presentations.

## Main results

* `CategoryTheory.preservesColimit_of_finallySmall`: a functor preserving filtered colimits of
  a given size preserves a filtered colimit over an index category which is merely locally
  small and finally small at that size.
* `CategoryTheory.Functor.CoconeTypes.IsColimit.comp_final`: a colimit cocone of types
  restricts along a final functor to a colimit cocone.

## Implementation notes

`CommRingCat.ringEquivOfIsColimit` builds the underlying bijection from the two colimit
comparison equivalences of types and then checks multiplicativity and additivity on the image
of the injections, which is where the filteredness of the index category is used: two elements
of the colimit come from a common stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w' r t

namespace CategoryTheory

/-- A functor that preserves filtered colimits of size `w` preserves every filtered colimit
whose index category is locally small and finally small at `w`: such a colimit is computed
over a `w`-small cofinal model. -/
theorem preservesColimit_of_finallySmall {J : Type u} [Category.{v} J] [IsFiltered J]
    [LocallySmall.{w} J] [FinallySmall.{w} J] {C : Type r} [Category C] {D : Type t}
    [Category D] (H : C ⥤ D) [PreservesFilteredColimitsOfSize.{w, w} H] (F : J ⥤ C) :
    PreservesColimit F H := by
  let K := (InitiallySmall.fromCofilteredInitialModel.{w} Jᵒᵖ).op ⋙ (opOpEquivalence J).functor
  exact Functor.Final.preservesColimit_of_comp K

/-- Restricting a colimit cocone of types along a final functor again gives a colimit
cocone. -/
theorem Functor.CoconeTypes.IsColimit.comp_final {J : Type u} [Category.{v} J] {K : Type w}
    [Category.{w'} K] {D : J ⥤ Type r} {c : D.CoconeTypes.{t}} (hc : c.IsColimit) (L : K ⥤ J)
    [L.Final] :
    (show (L ⋙ D).CoconeTypes.{t} from
      { pt := c.pt
        ι j := c.ι (L.obj j)
        ι_naturality f := c.ι_naturality (L.map f) }).IsColimit := by
  constructor
  convert hc.bijective.comp (L.bijective_colimitTypePrecomp D) using 1
  funext a
  obtain ⟨j, a, rfl⟩ := (L ⋙ D).ιColimitType_jointly_surjective a
  simp

end CategoryTheory

namespace CommRingCat

/-- A family of ring homomorphisms out of a diagram of commutative rings which is compatible
with the diagram, read as a cocone of types on the underlying type-valued diagram. -/
abbrev coconeTypesOfRingHoms {J : Type u} [Category.{v} J] (D : J ⥤ CommRingCat.{w})
    {R : Type r} [NonAssocSemiring R] (ι : ∀ j, D.obj j →+* R)
    (hι : ∀ {j k} (f : j ⟶ k), (ι k).comp (D.map f).hom = ι j) :
    (D ⋙ forget CommRingCat).CoconeTypes where
  pt := R
  ι j := ι j
  ι_naturality f := funext fun a ↦ DFunLike.congr_fun (hι f) a

/-- Two rings presented as the filtered colimit of the same diagram of commutative rings are
canonically isomorphic as rings, by the unique bijection compatible with the two families of
injections. -/
noncomputable def ringEquivOfIsColimit {J : Type u} [Category.{v} J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{w})
    {R : Type r} [NonAssocSemiring R] {T : Type t} [NonAssocSemiring T]
    (ι : ∀ j, D.obj j →+* R)
    (κ : ∀ j, D.obj j →+* T)
    (hι : ∀ {j k} (f : j ⟶ k), (ι k).comp (D.map f).hom = ι j)
    (hκ : ∀ {j k} (f : j ⟶ k), (κ k).comp (D.map f).hom = κ j)
    (hR : (coconeTypesOfRingHoms D ι hι).IsColimit)
    (hT : (coconeTypesOfRingHoms D κ hκ).IsColimit) :
    { e : R ≃+* T // ∀ j a, e (ι j a) = κ j a } := by
  let e : R ≃ T := hR.equiv.symm.trans hT.equiv
  have he (j) (a : D.obj j) : e (ι j a) = κ j a := by
    change hT.equiv (hR.equiv.symm ((coconeTypesOfRingHoms D ι hι).ι j a)) = _
    rw [hR.equiv_symm_ι_apply]
    exact (D ⋙ forget CommRingCat).descColimitType_ιColimitType_apply
      (coconeTypesOfRingHoms D κ hκ) j a
  refine ⟨{ e with map_mul' := ?_, map_add' := ?_ }, he⟩
  all_goals
    intro a b
    obtain ⟨j, a, rfl⟩ := hR.ι_jointly_surjective a
    obtain ⟨k, b, rfl⟩ := hR.ι_jointly_surjective b
    let l := IsFiltered.max j k
    let f : j ⟶ l := IsFiltered.leftToMax j k
    let g : k ⟶ l := IsFiltered.rightToMax j k
    dsimp only [coconeTypesOfRingHoms]
    first
    | change e (ι j a * ι k b) = e (ι j a) * e (ι k b)
    | change e (ι j a + ι k b) = e (ι j a) + e (ι k b)
    rw [← DFunLike.congr_fun (hι f) a, ← DFunLike.congr_fun (hι g) b]
    simp only [RingHom.comp_apply]
    first
    | rw [← map_mul, he, map_mul, he, he]
    | rw [← map_add, he, map_add, he, he]

end CommRingCat

end
