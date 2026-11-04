module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived

/-!
# Derived pushforward of derived sheaf Hom with exact support is derived internal Hom

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces. The right derived functor
`R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` of sheaf Hom with exact support, followed by derived
pushforward `Ri_* : D(𝒪_Z) ⥤ D(𝒪_X)`, is the right derived functor of the internal Hom
`ℰom_{𝒪_X}(i_* 𝒪_Z, -)` on `X`:

`Ri_* R ℰom(𝒪_Z, -) ≅ R ℰom_{𝒪_X}(i_* 𝒪_Z, -)` in `D(𝒪_X)`.

The underived statement is the internal Hom identification of [Stacks, Tag 0A75]: after
pushforward, sheaf Hom with exact support *is* the internal Hom from `i_* 𝒪_Z`. Passing to
derived functors is then formal, because `i_*` is exact and so does not need to be derived:
both sides of the displayed isomorphism are right derived functors of naturally isomorphic
functors on the homotopy category, and right derived functors are unique.

All names below live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main definitions

* `homSheafFromPushforwardStructureSheaf` is the internal Hom `ℰom_{𝒪_X}(i_* 𝒪_Z, -)`, an
  endofunctor of `𝒪_X`-modules.
* `derivedHomSheafFromPushforwardStructureSheaf` is its total right derived functor
  `R ℰom_{𝒪_X}(i_* 𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_X)`, and
  `derivedHomSheafFromPushforwardStructureSheafComparison` is the comparison map from the
  underived functor.
* `derivedModulePushforwardComparison` exhibits `Ri_* ∘ R ℰom(𝒪_Z, -)` as a right derived
  functor.
* `mapHomotopyCategoryPushforwardSheafHomExactSupportIso` is the underived identification of
  [Stacks, Tag 0A75] transported to the homotopy category.

## Main results

* `derivedModulePushforwardDerivedSheafHomExactSupportIso` is the isomorphism
  `Ri_* R ℰom(𝒪_Z, -) ≅ R ℰom_{𝒪_X}(i_* 𝒪_Z, -)` of [Stacks, Tag 0A77].
* `derivedModulePushforwardDerivedSheafHomExactSupportIso_fac_app` says that it is compatible
  with the two comparison maps out of the homotopy category, and
  `derivedModulePushforwardDerivedSheafHomExactSupportIso_uniq` and
  `existsUnique_derivedModulePushforwardDerivedSheafHomExactSupportIso` say that this
  compatibility determines it uniquely. This is the canonicality implicit in the equality sign
  of the statement.

## Implementation notes

Nothing is chosen: `R ℰom_{𝒪_X}(i_* 𝒪_Z, -)` is `Functor.totalRightDerived`, a Kan extension
along the localization, and `Ri_*` is `Functor.mapDerivedCategory` of the exact functor `i_*`.
The two derived functors exist because sheaves of modules form a Grothendieck abelian category,
so every complex admits a quasi-isomorphism into a K-injective complex ([Stacks, Tag 079P]).

That `Ri_* ∘ R ℰom(𝒪_Z, -)` is again a right derived functor is
`Stacks.DerivedFunctor.isRightDerivedFunctor_comp_mapDerivedCategory`: postcomposition with the
functor induced by an exact functor preserves the defining left Kan extension property, because
the pointwise colimit computing it has a terminal index, namely a K-injective resolution.
Exactness of `i_*` is [Stacks, Tag 08KS]; only the closed-embedding hypothesis enters there.

The identification of the two underived functors on the homotopy category is assembled from
`Functor.mapDerivedCategoryFactorsh`, which lets the exact functor `i_*` be moved across the
localization, and `Functor.mapHomotopyCategoryCompIso`, which transports the natural
isomorphism of [Stacks, Tag 0A75] from sheaves of modules to complexes up to homotopy.

## References

* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The internal Hom from `i_* 𝒪_Z` and its right derived functor -/

/-- The internal Hom `ℰom_{𝒪_X}(i_* 𝒪_Z, -)`, an endofunctor of `𝒪_X`-modules: the sheaf Hom
from the ring sheaf `i_* 𝒪_Z`, with its `i_* 𝒪_Z`-module structure restricted back to `𝒪_X`.

By the internal Hom identification of [Stacks, Tag 0A75] this is sheaf Hom with exact support
followed by pushforward. -/
noncomputable abbrev homSheafFromPushforwardStructureSheaf :
    SheafOfModules.{u} (structureSheafRing S.X) ⥤ SheafOfModules.{u} (structureSheafRing S.X) :=
  homSheaf (structureSheafHom S.i) ⋙ SheafOfModules.restrictScalars (structureSheafHom S.i)

/-- The internal Hom from `i_* 𝒪_Z` is additive: it is isomorphic to the composite of the two
additive functors `ℰom(𝒪_Z, -)` and `i_*`. -/
noncomputable instance additive_homSheafFromPushforwardStructureSheaf :
    S.homSheafFromPushforwardStructureSheaf.Additive :=
  Functor.additive_of_iso S.modulePushforwardSheafHomExactSupportIsoHomSheaf

/-- The internal Hom from `i_* 𝒪_Z` has a pointwise total right derived functor: sheaves of
modules form a Grothendieck abelian category, so every complex of them admits a
quasi-isomorphism into a K-injective complex. -/
instance hasPointwiseRightDerivedFunctor_homSheafFromPushforwardStructureSheaf :
    (S.homSheafFromPushforwardStructureSheaf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
          (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- The right derived functor `R ℰom_{𝒪_X}(i_* 𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_X)` of the internal Hom
from the ring sheaf `i_* 𝒪_Z`. -/
noncomputable abbrev derivedHomSheafFromPushforwardStructureSheaf :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) :=
  (S.homSheafFromPushforwardStructureSheaf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))

/-- The canonical map from the internal Hom from `i_* 𝒪_Z` to its right derived functor. -/
noncomputable abbrev derivedHomSheafFromPushforwardStructureSheafComparison :
    S.homSheafFromPushforwardStructureSheaf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ S.derivedHomSheafFromPushforwardStructureSheaf :=
  (S.homSheafFromPushforwardStructureSheaf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))

/-! ### Derived pushforward of the derived sheaf Hom is again a derived functor -/

/-- The comparison map exhibiting `Ri_* ∘ R ℰom(𝒪_Z, -)` as a derived functor: the comparison
map for `R ℰom(𝒪_Z, -)` pushed forward. -/
noncomputable abbrev derivedModulePushforwardComparison :
    (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        (modulePushforward S.i).mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙
        (S.derivedSheafHomExactSupport ⋙ (modulePushforward S.i).mapDerivedCategory) :=
  Functor.whiskerRight S.derivedSheafHomExactSupportComparison
      (modulePushforward S.i).mapDerivedCategory ≫
    (Functor.associator DerivedCategory.Qh S.derivedSheafHomExactSupport
      (modulePushforward S.i).mapDerivedCategory).hom

/-- `Ri_* ∘ R ℰom(𝒪_Z, -)` is a right derived functor of `ℰom(𝒪_Z, -)` followed by `Ri_*` on the
homotopy category.

Pushforward along a closed quotient morphism is exact ([Stacks, Tag 08KS]), and
postcomposition with the functor induced on derived categories by an exact functor preserves
the left Kan extension property defining a right derived functor, K-injective resolutions
([Stacks, Tag 079P]) providing a terminal index for the colimit that computes it. -/
instance isRightDerivedFunctor_derivedSheafHomExactSupport_comp_mapDerivedCategory :
    (S.derivedSheafHomExactSupport ⋙
      (modulePushforward S.i).mapDerivedCategory).IsRightDerivedFunctor
        S.derivedModulePushforwardComparison
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
          (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_comp_mapDerivedCategory
    S.sheafHomExactSupport S.derivedSheafHomExactSupport
    S.derivedSheafHomExactSupportComparison (modulePushforward S.i)
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- **[Stacks, Tag 0A75] on the homotopy category.** Sheaf Hom with exact support followed by
derived pushforward agrees, on complexes up to homotopy, with the internal Hom from
`i_* 𝒪_Z`.

The exact functor `i_*` is moved across the localization by
`Functor.mapDerivedCategoryFactorsh`, after which the internal Hom identification of
[Stacks, Tag 0A75] is applied degreewise. -/
noncomputable def mapHomotopyCategoryPushforwardSheafHomExactSupportIso :
    (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        (modulePushforward S.i).mapDerivedCategory ≅
      S.homSheafFromPushforwardStructureSheaf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.associator (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (modulePushforward S.i).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ))
      (modulePushforward S.i).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePushforward S.i).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso S.modulePushforwardSheafHomExactSupportIsoHomSheaf
        (ComplexShape.up ℤ)) DerivedCategory.Qh

/-! ### The identification of Tag 0A77 -/

/-- **Stacks Project, Tag 0A77.** For a closed quotient morphism `i : Z ⟶ X` of ringed spaces,
derived pushforward of the right derived sheaf Hom with exact support is the right derived
internal Hom from `i_* 𝒪_Z`:

`Ri_* R ℰom(𝒪_Z, K) ≅ R ℰom_{𝒪_X}(i_* 𝒪_Z, K)` naturally in `K ∈ D(𝒪_X)`.

Both sides are right derived functors — the left one because `i_*` is exact, so composing with
it preserves the property — of the two functors identified on the homotopy category by
`mapHomotopyCategoryPushforwardSheafHomExactSupportIso`, which is the underived identification
of [Stacks, Tag 0A75]. The isomorphism is the induced one on right derived functors. -/
@[stacks 0A77]
noncomputable def derivedModulePushforwardDerivedSheafHomExactSupportIso :
    S.derivedSheafHomExactSupport ⋙ (modulePushforward S.i).mapDerivedCategory ≅
      S.derivedHomSheafFromPushforwardStructureSheaf :=
  Functor.rightDerivedNatIso _ _ S.derivedModulePushforwardComparison
    S.derivedHomSheafFromPushforwardStructureSheafComparison
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))
    S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso

/-- **Stacks Project, Tag 0A77.** The isomorphism of [Stacks, Tag 0A77] is compatible with the
comparison maps out of the homotopy category and with the underived identification of
[Stacks, Tag 0A75]. -/
@[stacks 0A77 "compatibility of the isomorphism with the comparison maps"]
theorem derivedModulePushforwardDerivedSheafHomExactSupportIso_fac :
    S.derivedModulePushforwardComparison ≫
        Functor.whiskerLeft DerivedCategory.Qh
          S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom =
      S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom ≫
        S.derivedHomSheafFromPushforwardStructureSheafComparison :=
  Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) _

/-- The componentwise form of
`derivedModulePushforwardDerivedSheafHomExactSupportIso_fac`. -/
@[reassoc]
theorem derivedModulePushforwardDerivedSheafHomExactSupportIso_fac_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    S.derivedModulePushforwardComparison.app M ≫
        S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom.app
          (DerivedCategory.Qh.obj M) =
      S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom.app M ≫
        S.derivedHomSheafFromPushforwardStructureSheafComparison.app M :=
  Functor.rightDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
      (ComplexShape.up ℤ)) _ M

/-- **Stacks Project, Tag 0A77.** The isomorphism of [Stacks, Tag 0A77] is the unique one
compatible with the comparison maps out of the homotopy category. -/
@[stacks 0A77 "uniqueness of the isomorphism"]
theorem derivedModulePushforwardDerivedSheafHomExactSupportIso_uniq
    (e : S.derivedSheafHomExactSupport ⋙ (modulePushforward S.i).mapDerivedCategory ≅
      S.derivedHomSheafFromPushforwardStructureSheaf)
    (he : S.derivedModulePushforwardComparison ≫
        Functor.whiskerLeft DerivedCategory.Qh e.hom =
      S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom ≫
        S.derivedHomSheafFromPushforwardStructureSheafComparison) :
    e = S.derivedModulePushforwardDerivedSheafHomExactSupportIso := by
  refine Iso.ext (Functor.rightDerived_ext
    (RF := S.derivedSheafHomExactSupport ⋙ (modulePushforward S.i).mapDerivedCategory)
    (α := S.derivedModulePushforwardComparison)
    (W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
      (ComplexShape.up ℤ))
    _ e.hom S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom ?_)
  rw [he, S.derivedModulePushforwardDerivedSheafHomExactSupportIso_fac]

/-- There is a unique isomorphism `Ri_* R ℰom(𝒪_Z, -) ≅ R ℰom_{𝒪_X}(i_* 𝒪_Z, -)` compatible with
the comparison maps out of the homotopy category and with the underived identification of
[Stacks, Tag 0A75]. -/
theorem existsUnique_derivedModulePushforwardDerivedSheafHomExactSupportIso :
    ∃! e : S.derivedSheafHomExactSupport ⋙ (modulePushforward S.i).mapDerivedCategory ≅
      S.derivedHomSheafFromPushforwardStructureSheaf,
      S.derivedModulePushforwardComparison ≫
          Functor.whiskerLeft DerivedCategory.Qh e.hom =
        S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom ≫
          S.derivedHomSheafFromPushforwardStructureSheafComparison :=
  ⟨S.derivedModulePushforwardDerivedSheafHomExactSupportIso,
    S.derivedModulePushforwardDerivedSheafHomExactSupportIso_fac,
    fun e he => S.derivedModulePushforwardDerivedSheafHomExactSupportIso_uniq e he⟩

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
