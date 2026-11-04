module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayCoextensionIdempotent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksCore.Tactic.StacksAttribute

/-!
# Right orthogonality to `D(𝒪_f)` from right orthogonality to `𝒪_f`

Let `(𝒞, 𝒪)` be a ringed site, let `f` be a global section of `𝒪` and let `K ∈ D(𝒪)`.
[Stacks, Tag 0997] asserts the equivalence of

1. `R𝑆heafHom_𝒪(𝒪_f, K) = 0`,
2. `R𝑆heafHom_𝒪(L, K) = 0` for all `L` in `D(𝒪_f)`,
3. `T(K, f) = 0`.

This file proves the implication (1) ⇒ (2).

## Main results

* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_awayRestrictScalars_of_isZero`: if
  `R𝑆heafHom_𝒪(𝒪_f, K) = 0`, then `R𝑆heafHom_𝒪(L, K) = 0` for every `L` in `D(𝒪_f)`.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- Restriction of scalars along `𝒪 ⟶ 𝒪_f`, applied degreewise to complexes. -/
abbrev awayRestrictComplex :
    CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (awayRestrictScalars X h).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Coextension of scalars along `𝒪 ⟶ 𝒪_f`, applied degreewise to complexes. -/
abbrev awayCoextendComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)) ℤ :=
  coeffCoextendComplex X (awaySheaf h) (toAwaySheaf h)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- If a K-injective complex `J` of sheaves of `𝒪`-modules vanishes in the derived category, then
so does the internal Hom complex `SheafHom_𝒪(A, J)`, for every complex `A`. -/
theorem isZero_Q_sheafHomComplex_of_isZero
    (A J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective]
    (hJ : IsZero (DerivedCategory.Q.obj J)) :
    IsZero (DerivedCategory.Q.obj (sheafHomComplex X A J).obj) :=
  (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map_isZero hJ).of_iso
    (derivedSheafHomComparison X A J).symm

/-- The class of `𝒪_f`, read as `𝒪_f` restricted along `𝒪 ⟶ 𝒪_f` and placed in degree zero,
is `AlgebraicGeometry.RingedSite.derivedAwayModule`. -/
def awayRestrictStructureSheafQIso :
    DerivedCategory.Q.obj ((awayRestrictComplex X h).obj
        (structureSheafComplex (awayRingedSite X h))) ≅ derivedAwayModule X h :=
  letI : (awayRestrictScalars X h).Additive := SheafOfModules.instAdditiveRestrictScalars _
  ((awayRestrictScalars X h).mapDerivedCategoryFactors.app
      (structureSheafComplex (awayRingedSite X h))).symm ≪≫
    awayRestrictScalarsDerivedUnitIso X h

/-- If `R𝑆heafHom_𝒪(𝒪_f, K)` vanishes, then the coextension of scalars of the chosen K-injective
representative `I` of `K`, restricted back along `𝒪 ⟶ 𝒪_f`, vanishes in `D(𝒪)`. -/
theorem isZero_Q_awayRestrictCoextend_of_isZero_derivedSheafHom
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : IsZero (((derivedSheafHomBifunctor X).obj (op (derivedAwayModule X h))).obj K)) :
    IsZero (DerivedCategory.Q.obj ((awayRestrictComplex X h).obj
      ((awayCoextendComplex X h).obj (kInjectiveModel X K)))) := by
  set I := kInjectiveModel X K
  set S := structureSheafComplex (awayRingedSite X h)
  have h1 : IsZero (((derivedSheafHomBifunctor X).obj
      (op (derivedAwayModule X h))).obj (DerivedCategory.Q.obj I)) :=
    hK.of_iso (((derivedSheafHomBifunctor X).obj
      (op (derivedAwayModule X h))).mapIso (kInjectiveModelIso X K))
  have h2 : IsZero (((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj ((awayRestrictComplex X h).obj S)))).obj
        (DerivedCategory.Q.obj I)) :=
    h1.of_iso (((derivedSheafHomBifunctor X).mapIso
      (awayRestrictStructureSheafQIso X h).op).app (DerivedCategory.Q.obj I)).symm
  have h3 : IsZero (DerivedCategory.Q.obj
      (sheafHomComplex X ((awayRestrictComplex X h).obj S) I).obj) :=
    h2.of_iso (derivedSheafHomComparison X ((awayRestrictComplex X h).obj S) I).symm
  refine h3.of_iso (DerivedCategory.Q.mapIso ?_)
  exact (awayRestrictComplex X h).mapIso
      (structureSheafHomIso (awayRingedSite X h)
        ((awayCoextendComplex X h).obj I)).symm ≪≫
    coextHomComplexIso X (awaySheaf h) (toAwaySheaf h) S I

/-- If the coextension of scalars of a K-injective complex `I` of sheaves of `𝒪`-modules vanishes
in `D(𝒪)` after restriction along `𝒪 ⟶ 𝒪_f`, then so does the internal Hom complex
`SheafHom_𝒪(R M, I)` for every complex `M` of sheaves of `𝒪_f`-modules, where `R` is restriction
of scalars. -/
theorem isZero_Q_sheafHomComplex_awayRestrict_of_isZero
    (M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    (hI : IsZero (DerivedCategory.Q.obj
      ((awayRestrictComplex X h).obj ((awayCoextendComplex X h).obj I)))) :
    IsZero (DerivedCategory.Q.obj
      (sheafHomComplex X ((awayRestrictComplex X h).obj M) I).obj) := by
  have hepi : Epi (toAwaySheaf h) := epi_toAwaySheaf h
  set J := (awayRestrictComplex X h).obj ((awayCoextendComplex X h).obj I)
  have h1 : IsZero (DerivedCategory.Q.obj
      (sheafHomComplex X ((awayRestrictComplex X h).obj M) J).obj) :=
    isZero_Q_sheafHomComplex_of_isZero X ((awayRestrictComplex X h).obj M) J hI
  refine h1.of_iso (DerivedCategory.Q.mapIso ?_)
  refine (coextHomComplexIso X (awaySheaf h) (toAwaySheaf h) M I).symm ≪≫
    (awayRestrictComplex X h).mapIso
      (((sheafHomComplexBifunctor (awayRingedSite X h)).obj (op M)).mapIso
        (coextIdempotentComplexIso X (awaySheaf h) (toAwaySheaf h) I)) ≪≫
    coextHomComplexIso X (awaySheaf h) (toAwaySheaf h) M J

/-- Let `(𝒞, 𝒪)` be a ringed site, let `f` be a global section of `𝒪` and let `K ∈ D(𝒪)`. If
`R𝑆heafHom_𝒪(𝒪_f, K)` vanishes, then `R𝑆heafHom_𝒪(L, K)` vanishes for every object `L` of
`D(𝒪_f)`, viewed as an object of `D(𝒪)` by restriction of scalars. -/
@[stacks 0997 "(1) ⇒ (2)"]
theorem isZero_derivedSheafHom_awayRestrictScalars_of_isZero
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : IsZero (((derivedSheafHomBifunctor X).obj (op (derivedAwayModule X h))).obj K))
    (L : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O))) :
    IsZero (((derivedSheafHomBifunctor X).obj
      (op ((awayRestrictScalarsDerived X h).obj L))).obj K) := by
  let : (awayRestrictScalars X h).Additive := SheafOfModules.instAdditiveRestrictScalars _
  have : (DerivedCategory.Q (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O))).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)) (ComplexShape.up ℤ))
  set M := DerivedCategory.Q.objPreimage L
  have eL : DerivedCategory.Q.obj M ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have h1 : IsZero (DerivedCategory.Q.obj
      (sheafHomComplex X ((awayRestrictComplex X h).obj M) (kInjectiveModel X K)).obj) :=
    isZero_Q_sheafHomComplex_awayRestrict_of_isZero X h M (kInjectiveModel X K)
      (isZero_Q_awayRestrictCoextend_of_isZero_derivedSheafHom X h K hK)
  have h2 : IsZero (((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj ((awayRestrictComplex X h).obj M)))).obj
        (DerivedCategory.Q.obj (kInjectiveModel X K))) :=
    h1.of_iso (derivedSheafHomComparison X ((awayRestrictComplex X h).obj M)
      (kInjectiveModel X K))
  have eres : (awayRestrictScalarsDerived X h).obj L ≅
      DerivedCategory.Q.obj ((awayRestrictComplex X h).obj M) :=
    (awayRestrictScalarsDerived X h).mapIso eL.symm ≪≫
      (awayRestrictScalars X h).mapDerivedCategoryFactors.app M
  refine h2.of_iso (?_ ≪≫ (((derivedSheafHomBifunctor X).mapIso eres.op).app
    (DerivedCategory.Q.obj (kInjectiveModel X K))).symm)
  exact ((derivedSheafHomBifunctor X).obj
    (op ((awayRestrictScalarsDerived X h).obj L))).mapIso (kInjectiveModelIso X K).symm

end Derived

end AlgebraicGeometry.RingedSite

end
