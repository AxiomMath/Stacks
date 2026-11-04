module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DualizingTwistChart
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SliceChart

/-!
# A dualizing complex on `Spec R` is the associated sheaf of a complex over `R`

Let `R` be a Noetherian ring and `ω` a dualizing complex on `Spec R` (Stacks 0A87). Over the
affine open `⊤` it has a dualizing model `ω_Γ` over `Γ(Spec R, ⊤)`; restricting scalars along the
ring isomorphism `R ≅ Γ(Spec R, ⊤)` gives a complex `L` over `R` of finite injective dimension
with `L̃ ≅ ω`.

## Main results

* `AlgebraicGeometry.Space.exists_tilde_iso_of_isDualizingComplex`.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SpecModel

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Restriction of modules to the open `⊤` of a scheme is an equivalence. -/
def topRestrictEquiv (X : Scheme.{u}) : X.Modules ≌ (⊤ : X.Opens).toScheme.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι)
    (Scheme.Modules.restrictFunctor X.topIso.inv)
    ((Scheme.Modules.pullbackId X).symm ≪≫
      Scheme.Modules.pullbackCongr (Scheme.toIso_inv_ι X).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).symm ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback _).symm _)
    (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback _) _ ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback _) ≪≫
      Scheme.Modules.pullbackComp _ _ ≪≫
      Scheme.Modules.pullbackCongr (Scheme.ι_toIso_inv X) ≪≫ Scheme.Modules.pullbackId _)

/-- The ring isomorphism `R ≅ Γ(Spec R, ⊤)`. -/
abbrev φ : R ⟶ Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv

/-- **The associated sheaf of the restriction of scalars of a `Γ(Spec R, ⊤)`-module, restricted to
`⊤`, is its associated sheaf on `Spec Γ(Spec R, ⊤)` transported along `⊤ ≅ Spec Γ(Spec R, ⊤)`**,
naturally. -/
def restrictTopTildeNatIso :
    ModuleCat.restrictScalars (φ R).hom ⋙ tilde.functor R ⋙
        Scheme.Modules.restrictFunctor (⊤ : (Spec R).Opens).ι ≅
      tilde.functor Γ(Spec R, ⊤) ⋙
        Scheme.Modules.restrictFunctor (isAffineOpen_top (Spec R)).isoSpec.hom := by
  let e : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let Res := ModuleCat.restrictScalars (φ R).hom
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  -- extension of scalars along `φ` is the inverse of restriction of scalars
  let ε : ModuleCat.extendScalars (φ R).hom ≅ E.inverse :=
    (ModuleCat.extendRestrictScalarsAdj (φ R).hom).leftAdjointUniq E.symm.toAdjunction
  let θ₀ : tilde.functor R ⋙ Scheme.Modules.restrictFunctor (⊤ : (Spec R).Opens).ι ≅
      ModuleCat.extendScalars (φ R).hom ⋙ tilde.functor Γ(Spec R, ⊤) ⋙
        Scheme.Modules.restrictFunctor (isAffineOpen_top (Spec R)).isoSpec.hom :=
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback _ ≪≫
        Scheme.Modules.pullbackCongr (Stacks.Duality.isoSpec_hom_specMap_ΓSpecIso_inv R).symm ≪≫
        (Scheme.Modules.pullbackComp _ _).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackTildeIso R Γ(Spec R, ⊤) (φ R)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (Scheme.Modules.restrictFunctorIsoPullback _).symm)
  exact Functor.isoWhiskerLeft Res θ₀ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft Res ε ≪≫ E.unitIso.symm) _ ≪≫
    Functor.leftUnitor _

/-- **A dualizing complex on `Spec R` is the associated sheaf of a complex over `R` of finite
injective dimension.** -/
theorem exists_tilde_iso_of_isDualizingComplex (ω : RingedSite.SchemeStdDerived (Spec R))
    (hω : letI : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    ∃ (L : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)) (a b : ℤ),
      (letI := HasDerivedCategory.standard (ModuleCat.{u} R);
        StacksDraft.InjectiveDimension.HasInjectiveAmplitude L a b) ∧
      Nonempty (letI := HasDerivedCategory.standard (ModuleCat.{u} R);
        letI : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _;
        (tilde.functor R).mapDerivedCategory.obj L ≅ ω) := by
  let : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Spec R, ⊤))
  let := HasDerivedCategory.standard (⊤ : (Spec R).Opens).toScheme.Modules
  let := HasDerivedCategory.standard (Spec Γ(Spec R, ⊤)).Modules
  have : IsNoetherianRing Γ(Spec R, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨ωΓ, hωΓ, ⟨i⟩⟩ := hω ⊤ (isAffineOpen_top _)
  obtain ⟨a, b, I, hIa, hIb, hinj, ⟨eI⟩⟩ := hωΓ.finiteInjectiveDimension
  let e : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let Res := ModuleCat.restrictScalars (φ R).hom
  have : Res.IsEquivalence := E.isEquivalence_functor
  have : Res.Additive := inferInstance
  let L := Res.mapDerivedCategory.obj ωΓ
  refine ⟨L, a, b, ?_, ?_⟩
  · have := hIa
    have := hIb
    refine ⟨(Res.mapHomologicalComplex (ComplexShape.up ℤ)).obj I,
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff I Res a).2 hIa,
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff I Res b).2 hIb,
      fun k => (E.map_injective_iff _).2 (hinj k), ⟨Res.mapDerivedCategory.mapIso eI ≪≫
        Res.mapDerivedCategoryFactors.app I⟩⟩
  · let Rs := Scheme.Modules.restrictFunctor (⊤ : (Spec R).Opens).ι
    have hc := restrictTopTildeNatIso R
    let := Functor.additive_of_iso hc
    let := preservesFiniteLimits_of_natIso hc
    let := preservesFiniteColimits_of_natIso hc
    let j : Rs.mapDerivedCategory.obj ((tilde.functor R).mapDerivedCategory.obj L) ≅
        Rs.mapDerivedCategory.obj ω :=
      (Stacks.DerivedFunctor.mapDerivedCategoryCompIso (tilde.functor R) Rs).app L ≪≫
        (Stacks.DerivedFunctor.mapDerivedCategoryCompIso Res (tilde.functor R ⋙ Rs)).app ωΓ ≪≫
        (Stacks.DerivedGlueing.mapDerivedCategoryCongr hc).app ωΓ ≪≫ i.symm
    have : (topRestrictEquiv (Spec R)).functor.Additive :=
      inferInstanceAs (Scheme.Modules.restrictFunctor (⊤ : (Spec R).Opens).ι).Additive
    let F := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory (topRestrictEquiv (Spec R))
    exact ⟨F.fullyFaithfulFunctor.preimageIso j⟩

end AlgebraicGeometry.Space.SpecModel
