module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImageOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.DegreeZeroSurjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantPrimeToCharacteristicCurve

/-!
# `H¹(X, 𝐆_m) → H¹(U, 𝐆_m)` is surjective for an open `U` of a smooth curve

Let `X` be a smooth curve over an algebraically closed field and `U ⊆ X` a nonempty open
subscheme. The restriction map on étale cohomology `H¹(X, 𝐆_m) → H¹(U, 𝐆_m)` is surjective. In
terms of Picard groups (Tag 03P8) this is the surjectivity of `Pic(X) → Pic(U)`; here it is
proved directly on étale cohomology, from the divisor sequence of Stacks 03RI

`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} i_{x,*} 𝐙 → 0`

restricted to `U`: since `H¹(U, (j_* 𝐆_{m,η})|_U) = 0`, every class of `H¹(U, 𝐆_m)` is the
boundary of a section of `⨁_x i_{x,*} 𝐙` over `U`; such a section extends to `X` (the restriction
of sections of that sheaf from `X` to `U` is surjective); and boundaries commute with restriction.

With the Kummer sequence this gives statement (8) of Situation 0A52 for `𝐙/ℓ𝐙` on a smooth curve,
`ℓ` invertible in the base field, without any input on the Jacobian of `X`.

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_multiplicativeSheaf_opens`:
  **`H¹(X, 𝐆_m) → H¹(U, 𝐆_m)` is surjective.**
* `Stacks.EtaleCohomology.isDegreeTwoOpenRestrictionSurjective_constantSheaf_of_smoothCurve`:
  **statement (8) of Situation 0A52** for a constant sheaf cyclic of order `ℓ` invertible in `k`
  on a smooth curve over an algebraically closed field `k`.

## Implementation notes

The divisor sequence is available at the coefficient universe `u + 1`; it is carried to the
étale coefficient universe `max (u + 1) v` by the universe lift of the coefficients, which is
exact. The two vanishing and surjectivity inputs are proved at `u + 1` and transported.

## References

* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
* [Stacks Project, Tag 0A5A](https://stacks.math.columbia.edu/tag/0A5A)
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

open Stacks.Cohomology.CoefficientLift

/-- **`H¹(X, 𝐆_m) → H¹(U, 𝐆_m)` is surjective** for a nonempty open `U` of a smooth curve `X` over
an algebraically closed field, at the étale coefficient universe and in every `Ext` universe. -/
theorem surjective_etaleCohomologyRestrictionMap_multiplicativeSheaf_opens {k : Type u}
    [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (U : X.Opens) [Nonempty U]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} U.ι
      (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1) := by
  have : X.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{v, u + 1} :=
    (etaleUlift_properties.{u, u + 1, v} X).1
  have := uliftSheafCompose_preservesFiniteLimits.{u + 1, v} X.smallEtaleTopology
  have := uliftSheafCompose_preservesFiniteColimits.{u + 1, v} X.smallEtaleTopology
  let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{v, u + 1}
  let S := ShortComplex.mk
    (multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X))
    (divisorSequenceSecondMapOfCurve.{u, u + 1} g)
    (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1} g)
  have hS : S.ShortExact := shortExact_divisorSequenceOfCurve g
  have hS' : (S.map L).ShortExact := hS.map_of_exact L
  refine surjective_etaleCohomologyRestrictionMap_of_iso U.ι
    (multiplicativeSheafUliftIso.{u, v} X) 1 ?_
  refine surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_surjective_X₃ U.ι hS' 0 1
    rfl ?_ ?_
  · -- `H¹(U, (j_* 𝐆_{m,η})|_U) = 0`, transported from the coefficient universe `u + 1`.
    have e : (sheafCompose (U : Scheme.{u}).smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{v, u + 1}).obj ((etaleRestriction.{u, u + 1} U.ι).obj S.X₂) ≅
        (etaleAbelianInverseImage.{u, v} U.ι).obj (L.obj S.X₂) :=
      (fullyFaithfulSheafToPresheaf _ _).preimageIso
        (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)) ≪≫
      ((etaleAbelianInverseImageRestrictionIso.{u, v} U.ι).app (L.obj S.X₂)).symm
    exact subsingleton_sheafH_of_iso_ulift _ _ e 1
      (subsingleton_sheafH_etaleRestriction_genericPointDirectImage g U 1 le_rfl)
  · -- restriction of sections of `⨁_x i_{x,*} 𝐙` from `X` to `U` is surjective
    have hX : IsTerminal (Scheme.Etale.mk (𝟙 X)) := isTerminalEtaleMkId X
    refine surjective_etaleCohomologyRestrictionMap_zero_of_etale U.ι (L.obj S.X₃) hX ?_
    let W := (Scheme.Etale.smallEtaleCompose U.ι).obj
      ((smallEtaleBaseChange U.ι).obj (Scheme.Etale.mk (𝟙 X)))
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
    have : IsNoetherian X := { }
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
    have : CompactSpace U := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact _)
    have hsnd : IsIso (pullback.snd (𝟙 X) U.ι) := pullback_snd_iso_of_left_iso (𝟙 X) U.ι
    have hWhom : W.hom = pullback.snd (𝟙 X) U.ι ≫ U.ι := rfl
    have : CompactSpace W.left :=
      inferInstanceAs (CompactSpace ↥(pullback (𝟙 X) U.ι : Scheme.{u}))
    have : IsLocallyNoetherian W.left := isLocallyNoetherian_etale_left (X := X) W
    have : IsNoetherian W.left := { }
    have hinj : Function.Injective W.hom.base := fun p q h =>
      (ConcreteCategory.bijective_of_isIso (pullback.snd (𝟙 X) U.ι).base).1
        (U.ι.isOpenEmbedding.injective h)
    have hD := surjective_closedPointDivisorSheaf_map.{u + 1} X (hX.from W) hinj
    intro z
    obtain ⟨y, hy⟩ := hD z.down
    exact ⟨ULift.up y, congrArg ULift.up hy⟩

/-- **Stacks Project, Tag 0A5B, statement (8) in Case I (`ℓ` invertible in `k`).** Let `X` be a
smooth curve over an algebraically closed field `k`, `ℓ` invertible in `k` and `F` a constant
sheaf on `X_étale` whose value is cyclic of order `ℓ`. Then `H²(X, F) → H²(U, F)` is surjective
for every open `U ⊆ X`. -/
theorem isDegreeTwoOpenRestrictionSurjective_constantSheaf_of_smoothCurve {k : Type u}
    [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ)) :
    IsDegreeTwoOpenRestrictionSurjective.{u, v, w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) :=
  isDegreeTwoOpenRestrictionSurjective_constantSheaf_of_multiplicative g hℓk E hE
    fun U _ _ => surjective_etaleCohomologyRestrictionMap_multiplicativeSheaf_opens g U

end Stacks.EtaleCohomology

end
