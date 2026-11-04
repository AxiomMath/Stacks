module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients

/-!
# Stacks 095P for sheaves of abelian groups, with nothing assumed

Let `X` be a quasi-compact quasi-separated scheme of a big étale site and let
`F = colim_{i ∈ I} F_i` be a filtered colimit of abelian sheaves on `X_étale`. If `F` and all the
`F_i` are constructible, then the ind-object `F_i` is essentially constant with value `F`. This is
part (2) of Stacks 095P.

`AlgebraicGeometry.isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/EssentiallyConstantColimit.lean` is
this statement with Stacks 095N for `ℤ`-modules as the hypothesis `h095N`, in the shape
`HasFiniteShriekPresentation.{u, 0, u + 1}` at the ring `ℤ : Type 0`. That shape is not the one
the module development proves: the shriek-presentation route passes through `ModuleCat.free Λ`,
whose source `Type u ⥤ ModuleCat.{u} Λ` ties the module universe to the ring universe, so
Stacks 095N is available only for a Noetherian ring in `Type (u + 1)`.

The source's own proof of part (2) reduces it to part (1), a constructible abelian sheaf being
constructible as a sheaf of sets. The reduction used here is to part (3) instead, which is where
the library's compactness statement for abelian sheaves already lives: abelian groups are
`ULift ℤ`-modules by `AddCommGrpCat.moduleCatUliftIntEquivalence`, that ring *is* Noetherian in
`Type (u + 1)`, and `AlgebraicGeometry.isConstructibleModuleSheaf_uliftIntEquivalence` carries
constructibility across the induced equivalence of sheaf categories. So
`AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit`,
part (3) with nothing assumed, applies to the transported system, and the witness is brought
back by `CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith.of_equivalence`.

## Main results

* `AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit` —
  **Stacks 095P, part (2)**, with nothing assumed.

## Implementation notes

The two instance hypotheses — existence of the inverse image along a base change of small étale
sites, and sheafification over the slices — are assumed at `AddCommGrpCat.{u + 1}` only, which is
the coefficient category of the statement, and *derived* at `ModuleCat.{u + 1} (ULift.{u + 1} ℤ)`
by `CategoryTheory.Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence` and
`CategoryTheory.Sheaf.hasWeakSheafify_of_coefficientEquivalence`. Assuming them again at the
lifted ring would be a hypothesis no consumer can discharge.

## References

* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 05PU](https://stacks.math.columbia.edu/tag/05PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' v u

namespace AlgebraicGeometry

/-- The inverse image along a base change of small étale sites exists for sheaves of
`ULift ℤ`-modules as soon as it exists for abelian sheaves: the two coefficient categories are
equivalent. -/
public theorem isRightAdjoint_sheafPushforwardContinuous_uliftInt (B : BigEtaleSite.{u})
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    (S T : B.Scheme) (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint :=
  Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence _ _ _
    AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}

/-- Presheaves of `ULift ℤ`-modules over a slice of the small étale site have a sheafification as
soon as presheaves of abelian groups do. -/
public theorem hasWeakSheafify_over_uliftInt (B : BigEtaleSite.{u})
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]
    (T : B.Scheme) (V : SmallEtale B T.1 T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
  Sheaf.hasWeakSheafify_of_coefficientEquivalence _
    AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}

attribute [local instance 2000] isRightAdjoint_sheafPushforwardContinuous_uliftInt
  hasWeakSheafify_over_uliftInt

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Stacks 095P, part (2).** Let `X` be a quasi-compact quasi-separated scheme and let
`F = colim_{i ∈ I} F_i` be a filtered colimit of abelian sheaves on `X_étale`. If `F` and all the
`F_i` are constructible, then the ind-object `F_i` is essentially constant with value `F`.

Nothing is assumed. Abelian groups are `ULift ℤ`-modules, a ring which is Noetherian and lives in
the coefficient universe, so the system is carried to one of sheaves of modules by
`AlgebraicGeometry.isConstructibleModuleSheaf_uliftIntEquivalence`, part (3) of the tag applies to
it with nothing assumed, and the witness is brought back along the equivalence of sheaf
categories, which preserves the colimit and is fully faithful. -/
@[stacks 095P "part (2), sheaves of abelian groups"]
public theorem exists_isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit
    (X : B.Scheme) [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    {I : Type v} [Category.{v'} I] [IsFiltered I] [EssentiallySmall.{u + 1} I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (t : Cocone F) (ht : IsColimit t)
    (hF : ∀ i, IsConstructibleAbelianSheaf B X (F.obj i))
    (hcolim : IsConstructibleAbelianSheaf B X t.pt) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r := by
  let E := Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
    AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}
  let _ : PreservesColimit F E.functor :=
    E.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  obtain ⟨i, s, hs⟩ := exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit
    B X (ULift.{u + 1} ℤ) (F ⋙ E.functor) (E.functor.mapCocone t)
    (isColimitOfPreserves E.functor ht)
    (fun i => isConstructibleModuleSheaf_uliftIntEquivalence B X (F.obj i) (hF i))
    (isConstructibleModuleSheaf_uliftIntEquivalence B X t.pt hcolim)
  exact ⟨i, _, hs.of_equivalence E F t i s⟩

end AlgebraicGeometry

end
