module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiToposMorphism

/-!
# The abelian and derived direct image along `u_{X/S}`

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)`
be the morphism of topoi `Crystalline.GlobalCrystallineSituation.zariskiToposMorphism`. This file
constructs the direct image `u_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(X_Zar)` on abelian sheaves, its left
adjoint `u_{X/S}^{-1}`, the right derived functor `Ru_{X/S, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(X_Zar))`
and the higher direct images `R^j u_{X/S, *}`, and identifies derived crystalline global sections
with `Ru_{X/S, *}` followed by derived global sections on `X_Zar`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `opensTopology` — the small Zariski site `X_Zar` of `X`: the opens of `X` with
  `TopologicalSpace.Opens.grothendieckTopology`.
* `zariskiDirectImageCoeff` — the direct image `u_{X/S, *}` with coefficients in any category with
  the required limits.
* `zariskiDirectImage` — `u_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(X_Zar)`, the abelian direct image.
* `zariskiInverseImage` — `u_{X/S}^{-1} : Ab(X_Zar) ⥤ Ab(Cris(X/S))`, its left adjoint.
* `zariskiDirectImageAdjunction` — the adjunction `u^{-1} ⊣ u_*` on abelian sheaves.
* `hasDerivedCategoryZariskiSheaf` — a derived category of `Ab(X_Zar)` at the universe `u + 2`.
* `derivedZariskiDirectImageFunctor` — `Ru_{X/S, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(X_Zar))`.
* `derivedZariskiDirectImage` — `Ru_{X/S, *}` on a single abelian sheaf.
* `higherZariskiDirectImage` — `R^j u_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(X_Zar)`.
* `zariskiGlobalSections` and `derivedZariskiGlobalSectionsFunctor` — `Γ(X_Zar, -)` and
  `RΓ(X_Zar, -)`.

## Main results

* `zariskiInverseImage_exact` — `u_{X/S}^{-1}` on abelian sheaves is exact.
* `additive_zariskiDirectImage` and `preservesInjectiveObjects_zariskiDirectImage` — `u_{X/S, *}`
  is additive and carries injective abelian sheaves to injective abelian sheaves.
* `homologyZeroDerivedZariskiDirectImageIso` — `H^0(Ru_{X/S, *} -) ≅ u_{X/S, *}`, and
  `higherZariskiDirectImageZeroIso` the same for `R^0 u_{X/S, *}`.
* `isZero_higherZariskiDirectImage_of_injective` — `R^j u_{X/S, *} I = 0` for `j ≠ 0` and `I`
  injective.
* `zariskiDirectImage_obj_obj` and `zariskiDirectImageObjObjIsoLimit` — the presheaf underlying
  `u_{X/S, *} F` is the right Kan extension of [Stacks, Tag 00XK], so its sections over an open
  `V` of `X` are the limit of `F` over the objects `(U, T, δ)` of `Cris(X/S)` with `U ⊆ V`.
* `zariskiGlobalSectionsDirectImageIso` — `Γ(X_Zar, u_{X/S, *} -) ≅ Γ(Cris(X/S), -)`.
* `derivedGlobalSectionsIsoDerivedZariskiDirectImage` — [Stacks, Tag 015M] for `u_{X/S}`:
  `RΓ(Cris(X/S), -) ≅ Ru_{X/S, *} ⋙ RΓ(X_Zar, -)`, with
  `derivedGlobalSectionsIsoDerivedZariskiDirectImageObj` its form on a single abelian sheaf.

## References

* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe w w' w'' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The small Zariski site and its abelian sheaves -/

/-- **The small Zariski site `X_Zar` of the scheme of a global crystalline situation**: the
lattice of opens of `X` with its usual Grothendieck topology. -/
abbrev opensTopology : GrothendieckTopology S.X.Opens :=
  Opens.grothendieckTopology S.X.carrier

/-- Abelian sheaves on the small Zariski site of `X` admit sheafification at the coefficient
universe `u + 1`. -/
instance instHasSheafifyOpensAddCommGrpCat :
    HasSheafify (opensTopology S) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _

/-- Every presheaf on `Cris(X/S)` with values in a category with limits of size `(u, u + 1)` has
a pointwise right Kan extension along `(forgetToOpens S).op`. -/
instance instHasPointwiseRightKanExtensionForgetToOpens (E : Type (u + 2)) [Category.{u + 1} E]
    [HasLimitsOfSize.{u, u + 1} E] (F : (CrystallineThickening S)ᵒᵖ ⥤ E) :
    (forgetToOpens S).op.HasPointwiseRightKanExtension F :=
  fun _ => inferInstance

/-! ### The abelian direct and inverse image -/

/-- **The direct image `u_{X/S, *} : Sh(Cris(X/S)) ⥤ Sh(X_Zar)` with coefficients in `E`**: the
pushforward along the cocontinuous forgetful functor `forgetToOpens S`, for a category `E` with
the limits that compute the right Kan extension of [Stacks, Tag 00XK]. -/
abbrev zariskiDirectImageCoeff (E : Type (u + 2)) [Category.{u + 1} E]
    [HasLimitsOfSize.{u, u + 1} E] :
    Sheaf (smallTopology S) E ⥤ Sheaf (opensTopology S) E :=
  (forgetToOpens S).sheafPushforwardCocontinuous E (smallTopology S) (opensTopology S)

/-- **The abelian direct image `u_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(X_Zar)`**, which is
`zariskiDirectImageCoeff` at the coefficients `AddCommGrpCat.{u + 1}`. -/
def zariskiDirectImage :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (opensTopology S) AddCommGrpCat.{u + 1} :=
  (forgetToOpens S).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (smallTopology S) (opensTopology S)

/-- The abelian direct image is `zariskiDirectImageCoeff` at `AddCommGrpCat.{u + 1}`. -/
theorem zariskiDirectImage_eq :
    zariskiDirectImage S = zariskiDirectImageCoeff S AddCommGrpCat.{u + 1} :=
  rfl

/-- The pushforward of the morphism of topoi `u_{X/S}` is `zariskiDirectImageCoeff` at the
coefficients `Type (u + 1)`. -/
theorem zariskiToposMorphism_pushforward_eq :
    (zariskiToposMorphism S).pushforward = zariskiDirectImageCoeff S (Type (u + 1)) :=
  rfl

/-- **The abelian inverse image `u_{X/S}^{-1} : Ab(X_Zar) ⥤ Ab(Cris(X/S))`**: the sheafification
of the restriction of an abelian sheaf on the opens of `X` along `forgetToOpens S`. -/
def zariskiInverseImage :
    Sheaf (opensTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (forgetToOpens S).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
    (smallTopology S) (opensTopology S)

/-- The abelian inverse image `u_{X/S}^{-1}` is left adjoint to the abelian direct image
`u_{X/S, *}`. -/
def zariskiDirectImageAdjunction : zariskiInverseImage S ⊣ zariskiDirectImage S :=
  (forgetToOpens S).sheafAdjunctionPullbackCocontinuous AddCommGrpCat.{u + 1}
    (smallTopology S) (opensTopology S)

/-- `u_{X/S}^{-1}` on abelian sheaves is right exact, being a left adjoint. -/
instance preservesFiniteColimits_zariskiInverseImage :
    PreservesFiniteColimits (zariskiInverseImage S) :=
  inferInstanceAs (PreservesFiniteColimits
    ((forgetToOpens S).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
      (smallTopology S) (opensTopology S)))

/-- `u_{X/S}^{-1}` on abelian sheaves is left exact. -/
instance preservesFiniteLimits_zariskiInverseImage :
    PreservesFiniteLimits (zariskiInverseImage S) :=
  inferInstanceAs (PreservesFiniteLimits
    ((forgetToOpens S).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
      (smallTopology S) (opensTopology S)))

/-- **`u_{X/S}^{-1}` on abelian sheaves is exact.** -/
theorem zariskiInverseImage_exact :
    exactFunctor (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})
      (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (zariskiInverseImage S) :=
  ⟨preservesFiniteLimits_zariskiInverseImage S, preservesFiniteColimits_zariskiInverseImage S⟩

/-- `u_{X/S, *}` commutes with every limit that exists, being a right adjoint; in particular it
is left exact. -/
instance preservesLimitsOfSize_zariskiDirectImage :
    PreservesLimitsOfSize.{w, w'} (zariskiDirectImage S) :=
  (zariskiDirectImageAdjunction S).rightAdjoint_preservesLimits

/-- `u_{X/S, *}` is additive on abelian sheaves, being a right adjoint and hence preserving
binary products. -/
instance additive_zariskiDirectImage : (zariskiDirectImage S).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0} (zariskiDirectImage S) := inferInstance
  Functor.additive_of_preserves_binary_products _

/-- **`u_{X/S, *}` carries injective abelian sheaves to injective abelian sheaves.** -/
instance preservesInjectiveObjects_zariskiDirectImage :
    (zariskiDirectImage S).PreservesInjectiveObjects :=
  haveI : (zariskiInverseImage S).PreservesMonomorphisms := inferInstance
  preservesInjectiveObjects_of_preservesMonomorphisms_leftAdjoint _ _
    (zariskiDirectImageAdjunction S)

/-- **The presheaf underlying `u_{X/S, *} F` is the right Kan extension of the presheaf
underlying `F`** along `(forgetToOpens S).op`, definitionally. -/
theorem zariskiDirectImage_obj_obj (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((zariskiDirectImage S).obj F).obj = (forgetToOpens S).op.ran.obj F.obj :=
  rfl

/-- **The sections of `u_{X/S, *} F` over an open `V` of `X` are a limit over the objects of
`Cris(X/S)` lying in `V`**: the limit of `F` over `StructuredArrow (op V) (forgetToOpens S).op`,
the category of objects `(U, T, δ)` of `Cris(X/S)` together with an inclusion `U ⊆ V`. -/
def zariskiDirectImageObjObjIsoLimit
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (V : S.X.Opens) :
    ((zariskiDirectImage S).obj F).obj.obj (op V) ≅
      limit (StructuredArrow.proj (op V) (forgetToOpens S).op ⋙ F.obj) :=
  (forgetToOpens S).op.ranObjObjIsoLimit F.obj (op V)

/-! ### Global sections downstairs -/

/-- Abelian sheaves on the small Zariski site of `X` have enough injectives at the coefficient
universe `u + 1`. -/
instance instEnoughInjectivesOpens :
    EnoughInjectives (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u, u + 2} (opensTopology S)
    AddCommGrpCat.{u + 1}

/-- **The global sections functor `Γ(X_Zar, -)` of abelian sheaves on the small Zariski site of
`X`**, the right adjoint of the constant sheaf functor, at the coefficient universe `u + 1`. -/
abbrev zariskiGlobalSections :
    Sheaf (opensTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.Γ (opensTopology S) AddCommGrpCat.{u + 1}

/-- Global sections of abelian sheaves on the small Zariski site of `X` are additive, being a
right adjoint and hence preserving binary products. -/
instance additive_zariskiGlobalSections : (zariskiGlobalSections S).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u} (opensTopology S)

/-- **`Γ(X_Zar, u_{X/S, *} F) ≅ Γ(Cris(X/S), F)`**, naturally in the abelian sheaf `F`. -/
def zariskiGlobalSectionsDirectImageIso :
    zariskiDirectImage S ⋙ zariskiGlobalSections S ≅ globalSections S :=
  Functor.isoWhiskerLeft (zariskiDirectImage S)
      (Sheaf.ΓNatIsoLim (opensTopology S) AddCommGrpCat.{u + 1}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((forgetToOpens S).sheafPushforwardCocontinuousCompSheafToPresheafIso
        AddCommGrpCat.{u + 1} (smallTopology S) (opensTopology S)) lim ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
      (Functor.ranCompLimIso (H := AddCommGrpCat.{u + 1}) (forgetToOpens S).op) ≪≫
    (Sheaf.ΓNatIsoLim (smallTopology S) AddCommGrpCat.{u + 1}).symm

/-! ### The derived category of the Zariski side -/

/-- **A derived category of the abelian sheaves on the small Zariski site of `X`**, with its
morphisms in `Type (u + 2)`: the standard localization
`CategoryTheory.HasDerivedCategory.standard`. -/
@[instance_reducible]
def hasDerivedCategoryZariskiSheaf :
    HasDerivedCategory.{u + 2} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-! ### `Ru_{X/S, *}` -/

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The derived direct image `Ru_{X/S, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(X_Zar))`**: the right
derived functor of the abelian direct image `zariskiDirectImage`, between bounded below derived
categories. -/
def derivedZariskiDirectImageFunctor :
    DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  (zariskiDirectImage S).rightDerivedFunctorPlus

/-- **`Ru_{X/S, *} F` for a single abelian sheaf `F`**: the sheaf placed in degree zero, then the
derived direct image. -/
def derivedZariskiDirectImage :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
    derivedZariskiDirectImageFunctor S

/-- **The higher direct image `R^j u_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(X_Zar)`**, the degree-`j`
cohomology sheaf of `Ru_{X/S, *}`. -/
def higherZariskiDirectImage (j : ℤ) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (opensTopology S) AddCommGrpCat.{u + 1} :=
  (zariskiDirectImage S).rightDerivedPlus j

/-- The degree-`j` cohomology of `Ru_{X/S, *}` is `R^j u_{X/S, *}`, definitionally. -/
theorem derivedZariskiDirectImage_comp_homologyFunctor (j : ℤ) :
    derivedZariskiDirectImage S ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) j =
      higherZariskiDirectImage S j :=
  rfl

/-- **`R^j u_{X/S, *} I = 0` for `j ≠ 0` and `I` an injective abelian sheaf.** -/
theorem isZero_higherZariskiDirectImage_of_injective
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective F] (j : ℤ) (hj : j ≠ 0) :
    IsZero ((higherZariskiDirectImage S j).obj F) :=
  Functor.isZero_rightDerivedPlus_obj_injective (zariskiDirectImage S) j hj F

/-- **`R^0 u_{X/S, *} ≅ u_{X/S, *}`.** -/
def higherZariskiDirectImageZeroIso :
    higherZariskiDirectImage S 0 ≅ zariskiDirectImage S :=
  haveI : PreservesFiniteLimits (zariskiDirectImage S) := inferInstance
  (Stacks.DerivedIndexing.rightDerivedIso (zariskiDirectImage S) 0).symm ≪≫
    (zariskiDirectImage S).rightDerivedZeroIsoSelf

/-- **`H^0(Ru_{X/S, *} -) ≅ u_{X/S, *}`**, the derived-category form of
`higherZariskiDirectImageZeroIso`. -/
def homologyZeroDerivedZariskiDirectImageIso :
    derivedZariskiDirectImage S ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ((0 : ℕ) : ℤ) ≅
      zariskiDirectImage S :=
  higherZariskiDirectImageZeroIso S

end Derived

/-! ### `RΓ(Cris(X/S), -) ≅ Ru_{X/S, *}` followed by `RΓ(X_Zar, -)` -/

section Leray

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The derived global sections `RΓ(X_Zar, -) : D⁺(Ab(X_Zar)) ⥤ D⁺(Ab)` of the small Zariski
site of `X`.** -/
def derivedZariskiGlobalSectionsFunctor [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] :
    DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  (zariskiGlobalSections S).rightDerivedFunctorPlus

/-- **`RΓ(Cris(X/S), -) ≅ Ru_{X/S, *} ⋙ RΓ(X_Zar, -)`**: derived crystalline global sections
factor through the derived direct image along `u_{X/S}`. -/
def derivedGlobalSectionsIsoDerivedZariskiDirectImage
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] :
    derivedGlobalSectionsFunctor S ≅
      derivedZariskiDirectImageFunctor S ⋙ derivedZariskiGlobalSectionsFunctor S :=
  (Functor.rightDerivedFunctorPlusNatIso (zariskiGlobalSectionsDirectImageIso S)).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIso (zariskiDirectImage S) (zariskiGlobalSections S)

/-- `RΓ(Cris(X/S), F) ≅ RΓ(X_Zar, Ru_{X/S, *} F)` for a single abelian sheaf `F`, the
sheaf-level form of `derivedGlobalSectionsIsoDerivedZariskiDirectImage`. -/
def derivedGlobalSectionsIsoDerivedZariskiDirectImageObj
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] :
    derivedGlobalSections S ≅
      derivedZariskiDirectImage S ⋙ derivedZariskiGlobalSectionsFunctor S :=
  Functor.isoWhiskerLeft _ (derivedGlobalSectionsIsoDerivedZariskiDirectImage S) ≪≫
    (Functor.associator _ _ _).symm

end Leray

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
