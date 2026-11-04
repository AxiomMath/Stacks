module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeDeRhamDegreewise

/-!
# The base change predicate of [Stacks, Tag 07MU] at the zero map

`Crystalline.GlobalCrystallineSituation.SmallSite.IsBaseChangeIso07MU` is a predicate on a map

`φ : RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`

of `D(A)`, an element of the hom-group `...SmallSite.BaseChangeMap07MT`.  This file evaluates it,
together with its abelian degreewise and transported forms, at `φ = 0`: there the degree-`j`
clause asserts that a zero map is an isomorphism, which forces both of its ends to vanish.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `abelianBaseChangeCohomologyMap_zero` — the degree-`j` comparison of the abelian degreewise
  form is the zero map when `φ` is.
* `isZero_cohomology_of_abelianDegreewiseBaseChangeIso07MU_zero` and
  `isZero_homology_derivedBaseChangeTensorGlobalSections_of_zero` — under the nine hypotheses of
  the tag, the abelian degreewise form **at the zero map** forces `H^j(Cris(X/S), abelianSheaf
  F)` and `H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A)` to vanish in every degree `j : ℕ`.
* `not_abelianDegreewiseBaseChangeIso07MU_zero` and `not_isBaseChangeIso07MU_zero` — in any
  degree where the crystalline cohomology of `F` is nonzero, the abelian degreewise form and
  `IsBaseChangeIso07MU` fail at `φ = 0`.
* `transportedBaseChangeCohomologyMap_zero` and
  `not_transportedDegreewiseBaseChangeIso07MU_zero` — the same for the transport along an
  arbitrary comparison system `Γ`.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wS' wA wA'

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section ZeroMap

variable {S S' : GlobalCrystallineSituation.{u}} [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The degree-`j` comparison of the abelian degreewise form vanishes at the zero map.** -/
@[simp]
theorem abelianBaseChangeCohomologyMap_zero (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (j : ℕ) :
    abelianBaseChangeCohomologyMap f (0 : BaseChangeMap07MT f F' F) j = 0 := by
  rw [abelianBaseChangeCohomologyMap, Functor.map_zero, Functor.map_zero, zero_comp]

/-- **The crystalline cohomology of `F` vanishes if the abelian degreewise form of
[Stacks, Tag 07MU] holds at the zero map.** -/
theorem isZero_cohomology_of_abelianDegreewiseBaseChangeIso07MU_zero (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X) (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S))
    (h : AbelianDegreewiseBaseChangeIso07MU f g F' F (0 : BaseChangeMap07MT f F' F))
    (hp : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤))) (hqc : F'.IsQuasicoherentOnSite)
    (hcr : IsSheafCrystal F') (hqcpt : QuasiCompact S'.toClosedFiber)
    (hqsep : QuasiSeparated S'.toClosedFiber)
    (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
    (hflat : IsFlatModule S' F')
    (hlci : AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber)
    (htor : AlgebraicGeometry.TorIndependent S'.toClosedFiber
      (DividedPowerScheme.closedFiberMap f)) (j : ℕ) :
    IsZero ((cohomologyFunctor S j).obj (abelianSheaf F)) := by
  have hiso := (h hp hqc hcr hqcpt hqsep hpb hflat hlci htor).1 j
  rw [abelianBaseChangeCohomologyMap_zero] at hiso
  exact ((isIsoZero_iff_source_target_isZero _ _).1 hiso).2

/-- **The abelian group underlying the degree-`j` cohomology of
`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` vanishes for every `j : ℕ` if the abelian degreewise form of
[Stacks, Tag 07MU] holds at the zero map.** -/
theorem isZero_homology_derivedBaseChangeTensorGlobalSections_of_zero (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X) (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S))
    (h : AbelianDegreewiseBaseChangeIso07MU f g F' F (0 : BaseChangeMap07MT f F' F))
    (hp : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤))) (hqc : F'.IsQuasicoherentOnSite)
    (hcr : IsSheafCrystal F') (hqcpt : QuasiCompact S'.toClosedFiber)
    (hqsep : QuasiSeparated S'.toClosedFiber)
    (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
    (hflat : IsFlatModule S' F')
    (hlci : AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber)
    (htor : AlgebraicGeometry.TorIndependent S'.toClosedFiber
      (DividedPowerScheme.closedFiberMap f)) (j : ℕ) :
    IsZero ((forgetBaseAction S).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
        (derivedBaseChangeTensorGlobalSections f F'))) := by
  have hiso := (h hp hqc hcr hqcpt hqsep hpb hflat hlci htor).1 j
  rw [abelianBaseChangeCohomologyMap_zero] at hiso
  exact ((isIsoZero_iff_source_target_isZero _ _).1 hiso).1

/-- **The abelian degreewise form of [Stacks, Tag 07MU] is false at the zero map**, as soon as the
crystalline cohomology of `F` is nonzero in a single degree and the nine hypotheses of the tag
are available. -/
theorem not_abelianDegreewiseBaseChangeIso07MU_zero (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S))
    (hp : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤))) (hqc : F'.IsQuasicoherentOnSite)
    (hcr : IsSheafCrystal F') (hqcpt : QuasiCompact S'.toClosedFiber)
    (hqsep : QuasiSeparated S'.toClosedFiber)
    (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
    (hflat : IsFlatModule S' F')
    (hlci : AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber)
    (htor : AlgebraicGeometry.TorIndependent S'.toClosedFiber
      (DividedPowerScheme.closedFiberMap f)) (j : ℕ)
    (hne : ¬ IsZero ((cohomologyFunctor S j).obj (abelianSheaf F))) :
    ¬ AbelianDegreewiseBaseChangeIso07MU f g F' F (0 : BaseChangeMap07MT f F' F) := fun h =>
  hne (isZero_cohomology_of_abelianDegreewiseBaseChangeIso07MU_zero f g F' F h hp hqc hcr hqcpt
    hqsep hpb hflat hlci htor j)

/-- **`IsBaseChangeIso07MU` fails at the zero map**, as soon as the crystalline cohomology of `F`
is nonzero in a single degree and the nine hypotheses of the tag are available. -/
theorem not_isBaseChangeIso07MU_zero (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S))
    (hp : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤))) (hqc : F'.IsQuasicoherentOnSite)
    (hcr : IsSheafCrystal F') (hqcpt : QuasiCompact S'.toClosedFiber)
    (hqsep : QuasiSeparated S'.toClosedFiber)
    (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
    (hflat : IsFlatModule S' F')
    (hlci : AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber)
    (htor : AlgebraicGeometry.TorIndependent S'.toClosedFiber
      (DividedPowerScheme.closedFiberMap f)) (j : ℕ)
    (hne : ¬ IsZero ((cohomologyFunctor S j).obj (abelianSheaf F))) :
    ¬ IsBaseChangeIso07MU f g F' F (0 : BaseChangeMap07MT f F' F) := fun h =>
  not_abelianDegreewiseBaseChangeIso07MU_zero f g F' F hp hqc hcr hqcpt hqsep hpb hflat hlci
      htor j hne
    ((isBaseChangeIso07MU_iff_abelianDegreewise f g F' F (0 : BaseChangeMap07MT f F' F)).1 h)

/-! ### The transported form -/

/-- **The transported degree-`j` comparison also vanishes at the zero map**, for *every* named
model of `H^j(Cris(X/S), abelianSheaf F)`. -/
@[simp]
theorem transportedBaseChangeCohomologyMap_zero (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    {D : ℕ → AddCommGrpCat.{u + 1}}
    (Γ : ∀ j : ℕ, D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F)) (j : ℕ) :
    transportedBaseChangeCohomologyMap f (0 : BaseChangeMap07MT f F' F) Γ j = 0 := by
  rw [transportedBaseChangeCohomologyMap, abelianBaseChangeCohomologyMap_zero, zero_comp]

/-- **The transport of [Stacks, Tag 07MU] along any named comparison system is false at the zero
map**, under the same nonvanishing hypothesis as `not_abelianDegreewiseBaseChangeIso07MU_zero`. -/
theorem not_transportedDegreewiseBaseChangeIso07MU_zero (f : S.S ⟶ S'.S) (gX : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S)) {D : ℕ → AddCommGrpCat.{u + 1}}
    (Γ : ∀ j : ℕ, D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F))
    (hp : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤))) (hqc : F'.IsQuasicoherentOnSite)
    (hcr : IsSheafCrystal F') (hqcpt : QuasiCompact S'.toClosedFiber)
    (hqsep : QuasiSeparated S'.toClosedFiber)
    (hpb : IsPullback gX S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
    (hflat : IsFlatModule S' F')
    (hlci : AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber)
    (htor : AlgebraicGeometry.TorIndependent S'.toClosedFiber
      (DividedPowerScheme.closedFiberMap f)) (j : ℕ)
    (hne : ¬ IsZero ((cohomologyFunctor S j).obj (abelianSheaf F))) :
    ¬ TransportedDegreewiseBaseChangeIso07MU f gX F' F (0 : BaseChangeMap07MT f F' F) Γ :=
  fun h =>
    not_abelianDegreewiseBaseChangeIso07MU_zero f gX F' F hp hqc hcr hqcpt hqsep hpb hflat hlci
        htor j hne
      ((abelianDegreewiseBaseChangeIso07MU_iff_transported f gX F' F
        (0 : BaseChangeMap07MT f F' F) Γ).2 h)

end ZeroMap

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
