module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectGeneratorStep

/-!
# The elementary distinguished square step of Stacks 09IX

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces and let `Q`
be a perfect object of `D(𝒪_U)`. If there is a perfect object `B` of `D(𝒪_V)` whose restriction to
`U ×_X V` is `(Q ⊕ Q[1])|_{U ×_X V}`, then `Q ⊕ Q[1]` is the restriction to `U` of a perfect object
of `D(𝒪_X)`. This is the step of the proof of Stacks 09IV (with `E = 0` and no support condition),
which the source performs with Stacks 08EK on the affine `V` and then Stacks 08HB.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_shift_of_eds`: the statement
  above.

## References

* [Stacks Project, Tag 09IV](https://stacks.math.columbia.edu/tag/09IV)
* [Stacks Project, Tag 09IX](https://stacks.math.columbia.edu/tag/09IX)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The square step of Stacks 09IX.** Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished
square, `Q` a perfect object of `D(𝒪_U)` and `Bo` a perfect object of `D(𝒪_V)` with
`Bo|_{U ×_X V} ≅ Q|_{U ×_X V} ⊕ Q|_{U ×_X V}[1]`. Then there is a perfect object `F` of
`D(𝒪_X)` with `F|_U ≅ Q ⊕ Q[1]`: restriction commutes with sums and shifts, so the two objects
`Q ⊕ Q[1]` and `Bo` agree on `U ×_X V` and glue (Stacks 08HB). -/
theorem exists_isPerfect_restrict_iso_biprod_shift_of_eds
    (Q : DerivedCategory (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2))
    (hQ : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect Q)
    (Bo : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hB : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect Bo)
    (e : (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo ≅
      (edsRestrictFst B S hS hsq).mapDerivedCategory.obj Q ⊞
        ((edsRestrictFst B S hS hsq).mapDerivedCategory.obj Q)⟦(1 : ℤ)⟧) :
    ∃ F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F ∧
      Nonempty ((edsDerivedRestrictOpen B S hS hsq).obj F ≅ Q ⊞ Q⟦(1 : ℤ)⟧) := by
  let r := (edsRestrictFst B S hS hsq).mapDerivedCategory
  have : PreservesBinaryBiproducts r := preservesBinaryBiproducts_of_preservesBiproducts _
  let c : r.obj (Q ⊞ Q⟦(1 : ℤ)⟧) ≅ (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo :=
    r.mapBiprod Q (Q⟦(1 : ℤ)⟧) ≪≫ biprod.mapIso (Iso.refl _) ((r.commShiftIso (1 : ℤ)).app Q) ≪≫
      e.symm
  have hA : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPerfect (Q ⊞ Q⟦(1 : ℤ)⟧) :=
    RingedSite.isPerfect_biprod (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2) _ _ hQ (RingedSite.isPerfect_shift_general_of_hasDerivedCategory
        (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) Q hQ 1)
  obtain ⟨F, hF, hf, -⟩ := exists_isPerfect_glue_of_eds B S hS hsq _ Bo hA hB c
  exact ⟨F, hF, hf⟩

end Square

end AlgebraicGeometry.Space
