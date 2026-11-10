module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExactVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisStalkDegeneracies
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingAboveTheDimensionInduction

/-!
# Sections with support and cohomology with support, for modules on algebraic spaces

Let `X` be an algebraic space over a scheme `S`, `U ⊆ X` an open subspace and `Z = X ∖ U`.
For a sheaf of `𝒪_X`-modules `F` the sections with support in `Z` are the global sections
killed by restriction to `U`,

`Γ_Z(X, F) = Ker(Γ(X, F) ⟶ Γ(U, F|_U))`,

and the cohomology with support in `Z`, `H^q_Z(X, F)`, is the `q`-th right derived functor of
`Γ_Z(X, -)` on `𝒪_X`-modules (Stacks 0A4L, in the setting of modules).

On an injective module `I` restriction `Γ(X, I) ⟶ Γ(U, I|_U)` is onto, so
`0 ⟶ Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, (-)|_U) ⟶ 0` is short exact on injectives and gives the long
exact sequence of the pair
`⋯ ⟶ H^q_Z(X, F) ⟶ H^q(X, F) ⟶ H^q(U, F) ⟶ H^{q+1}_Z(X, F) ⟶ ⋯`.

The surjectivity on injectives is formal from one geometric input.  Global sections are maps
out of the structure sheaf `𝒪_X`, and restriction to `U` has a left adjoint `j_!`, extension by
zero; then `Γ(X, I) ⟶ Γ(U, I)` is precomposition with the counit `j_!(𝒪_X|_U) ⟶ 𝒪_X`, onto for
`I` injective as soon as that counit is a monomorphism
(`CategoryTheory.Adjunction.exists_comp_unit_app_eq_of_mono_counit`).  The counit is a
monomorphism because it is so on stalks at geometric points: an isomorphism over `U`, and with
vanishing source off `U`.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsAbRestrictionKer`: for an étale `j : Y ⟶ X`, the
  global sections killed by restriction along `j`, as an additive functor to abelian groups.

## Main results

* `AlgebraicGeometry.Space.mono_etaleModuleLowerShriekAdjunction_counit_edsOpenHom`: the counit
  of extension by zero along an open subspace is a monomorphism.
* `AlgebraicGeometry.Space.epi_globalSectionsAbRestriction_app_of_injective`: restriction of
  sections of an injective module to an open subspace is onto.
* `AlgebraicGeometry.Space.epi_globalSectionsAbRestriction_app_of_injective_of_isOpenImmersion`:
  the same along any open immersion.
* `AlgebraicGeometry.Space.shortExact_globalSectionsAbRestrictionKer_of_injective`: the sequence
  `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is short exact for `I` injective, and
  `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAbRestrictionKer_succ_of_epi` reads
  off the consequence of the long exact sequence of the pair used for Stacks 0A4R.

## Implementation notes

The open subspace is given by an open immersion `j : U ⟶ X`, `Z` being the complement of its
image.  Its image is presented, through `AlgebraicGeometry.Space.edsOpen`, as the open part
of the elementary distinguished square `(j(U) ⊆ X, X ⟶ X)`
(`AlgebraicGeometry.Space.isElementaryDistinguishedSquare_top`), where the stalks of extension
by zero are computed (`AlgebraicGeometry.Space.isIso_edsModuleStalk_edsOpen_counit_of_mem` and
`AlgebraicGeometry.Space.isZero_edsModuleStalk_edsOpen_shriek_of_notMem`).

The same groups for abelian sheaves at the coefficient universe `u + 1`, defined through
supports of sections, are `AlgebraicGeometry.Space.globalSectionsWithSupport` and
`AlgebraicGeometry.Space.cohomologyWithSupport`; the functors here are on `𝒪_X`-modules.

## References

* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sections killed by restriction -/

section Kernel

variable {Y X : AlgebraicSpaces B S hS}

/-- **The global sections killed by restriction along an étale morphism.**  For `j : Y ⟶ X`
étale, the functor `F ↦ Ker(Γ(X, F) ⟶ Γ(Y, F|_Y))` on `𝒪_X`-modules, valued in abelian groups;
for `j` the inclusion of an open subspace `U` these are the sections with support in `X ∖ U`. -/
def globalSectionsAbRestrictionKer (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u + 1} where
  obj M := AddCommGrpCat.of ((globalSectionsAbRestriction B S hS j hj).app M).hom.ker
  map {M N} φ := AddCommGrpCat.ofHom
    ((((globalSectionsAb B S hS X).map φ).hom.comp
        ((globalSectionsAbRestriction B S hS j hj).app M).hom.ker.subtype).codRestrict
      ((globalSectionsAbRestriction B S hS j hj).app N).hom.ker fun x => by
        have hx : ((globalSectionsAbRestriction B S hS j hj).app M).hom x.1 = 0 := x.2
        have h := congrArg (fun ψ => ψ.hom x.1)
          ((globalSectionsAbRestriction B S hS j hj).naturality φ)
        simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h
        change ((globalSectionsAbRestriction B S hS j hj).app N).hom
          (((globalSectionsAb B S hS X).map φ).hom x.1) = 0
        rw [h, hx, map_zero])
  map_id M := by
    ext x
    apply Subtype.ext
    simp
  map_comp φ ψ := by
    ext x
    apply Subtype.ext
    simp

/-- The functor of global sections killed by restriction is additive. -/
instance globalSectionsAbRestrictionKer_additive (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) :
    (globalSectionsAbRestrictionKer B S hS j hj).Additive where
  map_add {M N φ ψ} := by
    ext x
    apply Subtype.ext
    change ((globalSectionsAb B S hS X).map (φ + ψ)).hom x.1 =
      ((globalSectionsAb B S hS X).map φ).hom x.1 + ((globalSectionsAb B S hS X).map ψ).hom x.1
    rw [Functor.map_add]
    rfl

/-- The inclusion of the sections killed by restriction into all global sections. -/
def globalSectionsAbRestrictionKerι (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) :
    globalSectionsAbRestrictionKer B S hS j hj ⟶ globalSectionsAb B S hS X where
  app M := AddCommGrpCat.ofHom ((globalSectionsAbRestriction B S hS j hj).app M).hom.ker.subtype
  naturality _ _ _ := rfl

/-- The sections killed by restriction are killed by restriction. -/
theorem globalSectionsAbRestrictionKerι_comp (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) :
    globalSectionsAbRestrictionKerι B S hS j hj ≫ globalSectionsAbRestriction B S hS j hj = 0 :=
  NatTrans.ext (funext fun _ => AddCommGrpCat.ext fun x => x.2)

/-- **The sequence of sections killed by restriction is short exact where restriction is onto.**
If restriction `Γ(X, M) ⟶ Γ(Y, M|_Y)` is onto, then
`0 ⟶ Ker ⟶ Γ(X, M) ⟶ Γ(Y, M|_Y) ⟶ 0` is short exact. -/
theorem shortExact_globalSectionsAbRestrictionKer (j : Y ⟶ X) (hj : IsEtale B S hS j.hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : Epi ((globalSectionsAbRestriction B S hS j hj).app M)) :
    (NatTrans.appShortComplex (globalSectionsAbRestrictionKerι B S hS j hj)
      (globalSectionsAbRestriction B S hS j hj)
      (globalSectionsAbRestrictionKerι_comp B S hS j hj) M).ShortExact where
  exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  mono_f := (AddCommGrpCat.mono_iff_injective _).2 (AddSubgroup.subtype_injective _)
  epi_g := hM

end Kernel

/-! ### Surjectivity of restriction on injective modules -/

section Injective

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The counit of extension by zero along an open subspace is a monomorphism.**  For the open
part `U` of an elementary distinguished square and a sheaf of `𝒪_W`-modules `F`, the counit
`j_!(F|_U) ⟶ F` is a monomorphism. -/
theorem mono_etaleModuleLowerShriekAdjunction_counit_edsOpenHom
    (F : Modules.{u, u} B S hS W.1 W.2) :
    Mono ((etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).counit.app F) := by
  refine mono_of_mono_geometricModuleStalk B S hS W.1 W.2 (etaleRingSheaf B S hS W) _
    fun x => ?_
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)
  · have := isIso_edsModuleStalk_edsOpen_counit_of_mem B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)) F x hx
    infer_instance
  · have hz := isZero_edsModuleStalk_edsOpen_shriek_of_notMem B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)) F x hx
    exact ⟨fun g h _ => hz.eq_of_tgt g h⟩

/-- **Restriction of sections of an injective module to an open subspace is onto.**  For the
open part `U` of an elementary distinguished square and an injective `𝒪_W`-module `I`,
`Γ(W, I) ⟶ Γ(U, I|_U)` is onto. -/
theorem epi_globalSectionsAbRestriction_app_of_injective (I : Modules.{u, u} B S hS W.1 W.2)
    [Injective I] :
    Epi ((globalSectionsAbRestriction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).app I) := by
  have := mono_etaleModuleLowerShriekAdjunction_counit_edsOpenHom B S hS hsq
    (SheafOfModules.unit _)
  rw [AddCommGrpCat.epi_iff_surjective]
  intro t
  obtain ⟨b, hb⟩ := Adjunction.exists_comp_unit_app_eq_of_mono_counit
    (etaleModulePullbackAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)) I ((SheafOfModules.unitHomEquiv _).symm t)
  refine ⟨SheafOfModules.unitHomEquiv _ b, ?_⟩
  change SheafOfModules.sectionsMap _ (SheafOfModules.unitHomEquiv _ b) = t
  rw [← SheafOfModules.unitHomEquiv_comp_apply, hb]
  exact (SheafOfModules.unitHomEquiv _).apply_symm_apply t

/-- **The sequence of the pair on an injective module.**  For the open part `U` of an elementary
distinguished square and an injective `𝒪_W`-module `I`,
`0 ⟶ Γ_{W ∖ U}(W, I) ⟶ Γ(W, I) ⟶ Γ(U, I|_U) ⟶ 0` is short exact. -/
theorem shortExact_globalSectionsAbRestrictionKer_edsOpenHom_of_injective
    (I : Modules.{u, u} B S hS W.1 W.2) [Injective I] :
    (NatTrans.appShortComplex
      (globalSectionsAbRestrictionKerι B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (globalSectionsAbRestriction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (globalSectionsAbRestrictionKerι_comp B S hS _ _) I).ShortExact :=
  shortExact_globalSectionsAbRestrictionKer B S hS _ _ I
    (epi_globalSectionsAbRestriction_app_of_injective B S hS hsq I)

end Injective

/-! ### Restriction along an arbitrary open immersion -/

/-- An open subspace `U` of `X` and the identity of `X` form an elementary distinguished
square. -/
theorem isElementaryDistinguishedSquare_top {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U : Subfunctor X} (hU : IsOpenSubspace B S hS U) :
    IsElementaryDistinguishedSquare B S hS hX U (⊤ : Subfunctor X).ι :=
  isElementaryDistinguishedSquare_of_compl_subset B S hS hX U hU (isOpenSubspace_top hX).1 _
    (isOpenSubspace_top hX).2 fun x _ => pointsMap_surjective_of_isIso B S hS _ x

section OpenImmersion

variable {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
  (hje : IsEtale B S hS j.hom)

include hj in
/-- **Restriction of sections of an injective module along an open immersion is onto.**  For an
open immersion `j : U ⟶ X` and an injective `𝒪_X`-module `I`, `Γ(X, I) ⟶ Γ(U, I|_U)` is onto. -/
theorem epi_globalSectionsAbRestriction_app_of_injective_of_isOpenImmersion
    (I : Modules.{u, u} B S hS X.1 X.2) [Injective I] :
    Epi ((globalSectionsAbRestriction B S hS j hje).app I) := by
  have : Mono j.hom := mono_of_presheaf_isOpenImmersion hj
  have hsq := isElementaryDistinguishedSquare_top B S hS X.2
    (isOpenSubspace_range_of_isAlgebraicSpace B S hS U.2 _ hj)
  let eiso : U.1 ≅ (Subfunctor.range j.hom).toFunctor := asIso (Subfunctor.toRange j.hom)
  let e : U ⟶ edsOpen B S hS (W := X) hsq := ObjectProperty.homMk eiso.hom
  have : IsIso e := (ObjectProperty.isIso_hom_iff e).1 (inferInstanceAs (IsIso eiso.hom))
  have he : IsEtale B S hS e.hom := isEtale_of_isIso B S hS eiso.hom
  have he1 : e ≫ edsOpenHom B S hS (W := X) hsq = j :=
    ObjectProperty.hom_ext _ (Subfunctor.toRange_ι j.hom)
  have := isIso_etaleModulePullbackAdjunction_unit_of_isIso B S hS e he
  have h := congrArg (fun φ => φ.app I) (globalSectionsAbRestriction_comp B S hS e
    (edsOpenHom B S hS (W := X) hsq) he (isEtale_edsOpenHom B S hS (W := X) hsq) he1 hje)
  simp only [NatTrans.comp_app] at h
  rw [h]
  have := epi_globalSectionsAbRestriction_app_of_injective B S hS (W := X) hsq I
  refine epi_comp' inferInstance (epi_comp' ?_ ?_)
  · simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  · simp only [Functor.whiskerRight_app]
    infer_instance

include hj in
/-- **The sequence of the pair on an injective module.**  For an open immersion `j : U ⟶ X`
and an injective `𝒪_X`-module `I`, `0 ⟶ Γ_{X ∖ U}(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I|_U) ⟶ 0` is short
exact. -/
theorem shortExact_globalSectionsAbRestrictionKer_of_injective
    (I : Modules.{u, u} B S hS X.1 X.2) [Injective I] :
    (NatTrans.appShortComplex (globalSectionsAbRestrictionKerι B S hS j hje)
      (globalSectionsAbRestriction B S hS j hje)
      (globalSectionsAbRestrictionKerι_comp B S hS j hje) I).ShortExact :=
  shortExact_globalSectionsAbRestrictionKer B S hS j hje I
    (epi_globalSectionsAbRestriction_app_of_injective_of_isOpenImmersion B S hS j hj hje I)

include hj in
/-- **Dimension shifting along the sequence of the pair.**  For an open immersion `j : U ⟶ X`
and an `𝒪_X`-module `F`, if `Hⁿ⁺¹(X, F) = 0` and restriction `Hⁿ(X, F) ⟶ Hⁿ(U, F|_U)` is onto,
then `Hⁿ⁺¹_{X ∖ U}(X, F) = 0`. -/
theorem isZero_rightDerived_globalSectionsAbRestrictionKer_succ_of_epi
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (hG : IsZero (((globalSectionsAb B S hS X).rightDerived (n + 1)).obj F))
    (hres : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) n).app F)) :
    IsZero (((globalSectionsAbRestrictionKer B S hS j hje).rightDerived (n + 1)).obj F) :=
  isZero_rightDerived_succ_of_epi _ _ (globalSectionsAbRestrictionKerι_comp B S hS j hje)
    (fun I _ => shortExact_globalSectionsAbRestrictionKer_of_injective B S hS j hj hje I)
    F n hG hres

end OpenImmersion

end AlgebraicGeometry.Space

end
