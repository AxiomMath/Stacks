module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# The reduced closed subscheme supported on a closed subset

Every closed subset `Z` of a scheme `X` carries exactly one reduced closed subscheme structure,
namely the one cut out by the vanishing ideal sheaf of `Z`. Dually, a morphism from a *reduced*
scheme factors through a closed subscheme of `X` precisely when its set-theoretic image is
contained in the underlying closed subset, and in particular every morphism from a reduced
scheme factors uniquely through the reduction of its target.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme`: an ideal
  sheaf whose support is `Z` and whose closed subscheme is reduced is the vanishing ideal sheaf
  of `Z`. Together with the existence statements recorded for tag `01J3` this says that the
  reduced induced structure on a closed subset is unique.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support`: a
  morphism from a reduced scheme factors through a closed subscheme exactly when its image lies
  in the support of that subscheme.
* `AlgebraicGeometry.Scheme.existsUnique_lift_nilradical_subschemeι`: every morphism from a
  reduced scheme factors uniquely through the reduction of its target.

## Implementation notes

Closed subschemes are represented by their ideal sheaves, so uniqueness of the reduced closed
subscheme structure on `Z` is stated as an equality of ideal sheaves rather than an equivalence
of closed immersions. The existence half of tag `01J3` — the construction of the vanishing ideal
sheaf, the identification of its support, and the reducedness of the resulting subscheme — is
already available, and is registered against the tag rather than restated.

The reduction of `X` is the closed subscheme cut out by `X.nilradical`, which is the vanishing
ideal sheaf of the whole space. Its inclusion is a closed immersion, hence a monomorphism, which
is what turns the factorization of tag `0356` into a unique factorization.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

add_to_stacks 01J3 "canonical construction"
  AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
add_to_ega "I 10.8.1" AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
add_to_ega "III 5.3.5" AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
add_to_stacks 01J3 "underlying closed subset"
  AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal
add_to_ega "I 10.8.1" "more general"
  AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal
add_to_ega "III 5.3.5" "partial" AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal
add_to_stacks 01J3 "reducedness"
  AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal

namespace Scheme.IdealSheafData

/-- A reduced closed subscheme structure on a closed subset is its vanishing-ideal structure. -/
@[stacks 01J3 "uniqueness", ega "I 5.1.2" "uniqueness", ega "I 5.2.1" "closed case, uniqueness"]
theorem eq_vanishingIdeal_of_isReduced_subscheme {X : Scheme.{u}}
    (I : X.IdealSheafData) (T : Closeds X) (hT : I.support = T)
    [IsReduced I.subscheme] : I = Scheme.IdealSheafData.vanishingIdeal T := by
  rw [← hT, vanishingIdeal_support]
  apply Scheme.IdealSheafData.ext
  funext U
  change I.ideal U = (I.ideal U).radical
  let V : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U.1
  have hVaff : IsAffineOpen V := IsAffineOpen.preimage U.2 I.subschemeι
  have : IsReduced (V : Scheme) := isReduced_of_isOpenImmersion V.ι
  have : _root_.IsReduced Γ(I.subscheme, V) :=
    (affine_isReduced_iff (.of Γ(I.subscheme, V))).mp
      (isReduced_of_isOpenImmersion hVaff.isoSpec.inv)
  exact ((Ideal.isRadical_iff_quotient_reduced _).2
    (isReduced_of_injective
      (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.toRingHom
      (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective)).radical.symm

/-- A map from a reduced scheme factors through a closed subscheme precisely when its
set-theoretic image lies in the support of that subscheme. -/
@[stacks 0356 "factorization criterion",
  ega "I 5.2.2" "more general",
  sga "3 VIB 7.3.0" "factorization criterion", sga "3 VIB 7.1" "partial"]
theorem exists_lift_subschemeι_iff_range_subset_support {X Y : Scheme.{u}}
    [IsReduced Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (∃ g : Y ⟶ I.subscheme, g ≫ I.subschemeι = f) ↔
      Set.range f ⊆ (I.support : Set X) := by
  constructor
  · rintro ⟨g, rfl⟩ y ⟨x, rfl⟩
    change I.subschemeι (g x) ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨g x, rfl⟩
  · intro h
    have hker : I ≤ f.ker := by
      apply (le_support_iff_le_vanishingIdeal.mp (Closeds.closure_le.mpr h)).trans
      simpa only [vanishingIdeal_top, Scheme.nilradical_eq_bot, IdealSheafData.map_bot,
        Closeds.coe_top, Set.image_univ] using (map_vanishingIdeal f (⊤ : Closeds Y)).symm.le
    exact ⟨IsClosedImmersion.lift I.subschemeι f (by simpa [I.ker_subschemeι] using hker),
      IsClosedImmersion.lift_fac I.subschemeι f _⟩

end Scheme.IdealSheafData

/-- Every map from a reduced scheme factors uniquely through the reduction of its target. -/
@[stacks 0356 "factorization through the reduction",
  ega "I 5.1.5" "reduced source factors",
  ega "I 4.1.8" "special case"]
theorem Scheme.existsUnique_lift_nilradical_subschemeι {X Y : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) :
    ∃! g : Y ⟶ X.nilradical.subscheme, g ≫ X.nilradical.subschemeι = f := by
  obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    X.nilradical f).2 (by simp)
  exact ⟨g, hg, fun g' hg' => (cancel_mono X.nilradical.subschemeι).mp (hg'.trans hg.symm)⟩

end AlgebraicGeometry
