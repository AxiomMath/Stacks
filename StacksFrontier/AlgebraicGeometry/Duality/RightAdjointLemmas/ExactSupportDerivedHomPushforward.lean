module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso

/-!
# Derived internal Hom out of a derived pushforward along a closed quotient morphism

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is exact and left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)`. For `M` in `D(𝒪_Z)` and `K` in `D(𝒪_X)` the derived
internal Hom out of `Ri_* M` is the pushforward of a derived internal Hom computed on `Z`:

`R ℋom_{𝒪_X}(Ri_* M, K) ≅ Ri_* R ℋom_{𝒪_Z}(M, R ℰom(𝒪_Z, K))` in `D(𝒪_X)`.

The mechanism is the one of [Stacks, Tag 0E2I]. Derived internal Hom is computed by a K-injective
representative of its target, and sheaf Hom with exact support carries K-injective complexes to
K-injective complexes because its left adjoint `i_*` is exact ([Stacks, Tag 08BJ]). Hence, for a
K-injective complex `𝒦` of `𝒪_X`-modules and any complex `ℳ` of `𝒪_Z`-modules, both sides of the
displayed isomorphism are classes of ordinary internal Hom complexes: the left-hand side is the
class of `ℋom^•_{𝒪_X}(i_* ℳ, 𝒦)` and the right-hand side is the class of
`i_* ℋom^•_{𝒪_Z}(ℳ, ℰom(𝒪_Z, 𝒦))`. The identification of those two complexes is the internal
form of the adjunction of [Stacks, Tag 0A75]; it is an underived statement, and it enters below as
the hypothesis `hom`.

All names live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main definitions

* `ambientSite` and `closedSite` read the two ringed spaces as ringed sites, which is the setting
  of the derived internal Hom bifunctor.
* `siteModulePushforward`, `siteSheafHomExactSupport` and `siteDerivedSheafHomExactSupport` are
  `i_*`, `ℰom(𝒪_Z, -)` and `R ℰom(𝒪_Z, -)` with their types written over the ring sheaves of
  those sites, as `siteModulePushforward_eq`, `siteSheafHomExactSupport_eq` and
  `siteDerivedSheafHomExactSupport_eq` record.
* `derivedSheafHomExactSupportIsoOfIsKInjective` computes `R ℰom(𝒪_Z, -)` on a K-injective
  complex by the underived functor.

## Main results

* `isKInjective_mapHomologicalComplex_siteSheafHomExactSupport`: sheaf Hom with exact support
  preserves K-injectivity of complexes. This is [Stacks, Tag 08BJ] applied to the adjunction of
  [Stacks, Tag 0A75], whose left adjoint is exact by [Stacks, Tag 08KS].
* `derivedSheafHomDerivedModulePushforwardIso`: the isomorphism of [Stacks, Tag 0E2I], granted
  the underived identification of internal Hom complexes described above.

## Implementation notes

Nothing is chosen beyond the chosen functorial K-injective resolution that the derived internal
Hom bifunctor is itself built from: the representatives of `M` and `K` used in the construction
are `AlgebraicGeometry.RingedSite.kInjectiveModel`, the same device that defines the bifunctor,
and `Ri_*` is `CategoryTheory.Functor.mapDerivedCategory` of the exact functor `i_*`.

The pushforward, the sheaf Hom with exact support and its right derived functor are retyped over
`AlgebraicGeometry.RingedSite.ringSheaf` of the ringed site of the space rather than over
`structureSheafRing`. The two ring sheaves are the same expression, and each
`_eq` lemma below is `rfl`, but `structureSheafRing` is a `def` and typeclass
synthesis does not unfold it: with a complex typed over it, the K-injectivity hypothesis of
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison` cannot be discharged. The retyping is
what lets the exact-support complex appear as a K-injective target of the internal Hom complex.

The conclusion is stated for each pair of objects separately rather than as an isomorphism of
bifunctors, which is the form of the source statement.

## References

* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The two ringed spaces as ringed sites -/

/-- The ambient ringed space `X`, read as a ringed site: the site of its opens with the
open-cover topology, together with its structure sheaf. -/
abbrev ambientSite : RingedSite.{u, u, u} := Stacks.SheafOfModules.ringedSite S.X.sheaf

/-- The closed ringed subspace `Z`, read as a ringed site. -/
abbrev closedSite : RingedSite.{u, u, u} := Stacks.SheafOfModules.ringedSite S.Z.sheaf

/-- Pushforward `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)`, with its type written over the ring sheaves of the
two ringed sites. -/
def siteModulePushforward :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O) :=
  modulePushforward S.i

/-- Sheaf Hom with exact support `ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)` of [Stacks, Tag 0A75],
with its type written over the ring sheaves of the two ringed sites. -/
def siteSheafHomExactSupport :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O) :=
  S.sheafHomExactSupport

/-- The retyped pushforward is the pushforward of [Stacks, Tag 0096]. -/
theorem siteModulePushforward_eq : S.siteModulePushforward = modulePushforward S.i := rfl

/-- The retyped sheaf Hom with exact support is the functor of [Stacks, Tag 0A75]. -/
theorem siteSheafHomExactSupport_eq : S.siteSheafHomExactSupport = S.sheafHomExactSupport := rfl

/-- Additivity of `i_*`, registered at the retyped functor, which is what
`CategoryTheory.Functor.mapHomologicalComplex` and `CategoryTheory.Functor.mapDerivedCategory`
consume. -/
instance additive_siteModulePushforward : S.siteModulePushforward.Additive :=
  inferInstanceAs (modulePushforward S.i).Additive

/-- Additivity of `ℰom(𝒪_Z, -)`, registered at the retyped functor. -/
instance additive_siteSheafHomExactSupport : S.siteSheafHomExactSupport.Additive :=
  inferInstanceAs S.sheafHomExactSupport.Additive

/-- Left exactness of `i_*`, registered at the retyped functor. -/
instance preservesFiniteLimits_siteModulePushforward :
    PreservesFiniteLimits S.siteModulePushforward :=
  inferInstanceAs (PreservesFiniteLimits (modulePushforward S.i))

/-- Right exactness of `i_*` along a closed quotient morphism ([Stacks, Tag 08KS]), registered at
the retyped functor. -/
instance preservesFiniteColimits_siteModulePushforward :
    PreservesFiniteColimits S.siteModulePushforward :=
  inferInstanceAs (PreservesFiniteColimits (modulePushforward S.i))

/-- The adjunction `i_* ⊣ ℰom(𝒪_Z, -)` of [Stacks, Tag 0A75], retyped. -/
def siteAdjunction : S.siteModulePushforward ⊣ S.siteSheafHomExactSupport :=
  S.modulePushforwardSheafHomExactSupportAdjunction

/-- The derived pushforward `Ri_*` of [Stacks, Tag 0A76] is the functor induced on derived
categories by the retyped pushforward. -/
theorem siteModulePushforward_mapDerivedCategory_eq :
    S.siteModulePushforward.mapDerivedCategory = (modulePushforward S.i).mapDerivedCategory :=
  rfl

/-- The right derived functor `R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` of [Stacks, Tag 0A76], with its
type written over the ring sheaves of the two ringed sites. -/
def siteDerivedSheafHomExactSupport :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O)) :=
  S.derivedSheafHomExactSupport

/-- The retyped right derived functor is the one of [Stacks, Tag 0A76]. -/
theorem siteDerivedSheafHomExactSupport_eq :
    S.siteDerivedSheafHomExactSupport = S.derivedSheafHomExactSupport := rfl

/-! ### Sheaf Hom with exact support preserves K-injective complexes -/

/-- **Stacks Project, Tag 08BJ for sheaf Hom with exact support.** If `𝒦` is a K-injective
complex of `𝒪_X`-modules then `ℰom(𝒪_Z, 𝒦)` is a K-injective complex of `𝒪_Z`-modules: sheaf
Hom with exact support is the right adjoint of the exact functor `i_*`. -/
instance isKInjective_mapHomologicalComplex_siteSheafHomExactSupport
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact S.siteSheafHomExactSupport
    S.siteModulePushforward S.siteAdjunction I

/-- A K-injective complex computes the right derived functor of sheaf Hom with exact support:
`R ℰom(𝒪_Z, -)` at the class of a K-injective complex `𝒦` is the class of `ℰom(𝒪_Z, 𝒦)`. -/
def derivedSheafHomExactSupportIsoOfIsKInjective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O)) ℤ) [hI : I.IsKInjective] :
    DerivedCategory.Q.obj
        ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      S.siteDerivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I) :=
  letI : CochainComplex.IsKInjective
    (show CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ from I) := hI
  have hiso := Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective
    (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    S.derivedSheafHomExactSupport S.derivedSheafHomExactSupportComparison I
  (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).symm.app
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
    DerivedCategory.Qh.mapIso
      ((S.sheafHomExactSupport.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm ≪≫
    @asIso _ _ _ _ _ hiso ≪≫
    S.derivedSheafHomExactSupport.mapIso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.X))).app I)

/-! ### Derived internal Hom out of a derived pushforward -/

/-- The isomorphism

`R ℋom_{𝒪_X}(Ri_* M, K) ≅ Ri_* R ℋom_{𝒪_Z}(M, R ℰom(𝒪_Z, K))`

computed from a complex `N` representing `M` and a K-injective complex `I` representing `K`,
granted the underived identification `hom` of internal Hom complexes, which says that for
complexes `ℳ` of `𝒪_Z`-modules and `𝒦` of `𝒪_X`-modules the pushforward of
`ℋom^•_{𝒪_Z}(ℳ, ℰom(𝒪_Z, 𝒦))` is `ℋom^•_{𝒪_X}(i_* ℳ, 𝒦)`. That identification is the internal
form of the adjunction of [Stacks, Tag 0A75].

Both sides are read off from those representatives: the derived internal Hom is computed by a
K-injective target, `ℰom(𝒪_Z, 𝒦)` is again K-injective by
`isKInjective_mapHomologicalComplex_siteSheafHomExactSupport`, and it computes `R ℰom(𝒪_Z, -)` by
`derivedSheafHomExactSupportIsoOfIsKInjective`; the exact functor `i_*` passes through the
localization. -/
def derivedSheafHomDerivedModulePushforwardIsoOfModels
    (hom : ∀ (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O)) ℤ)
      (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O)) ℤ),
      (S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (RingedSite.sheafHomComplex S.closedSite N
            ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≅
        (RingedSite.sheafHomComplex S.ambientSite
          ((S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) I).obj)
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O))}
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O))}
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O)) ℤ) [hI : I.IsKInjective]
    (eM : M ≅ DerivedCategory.Q.obj N) (eK : K ≅ DerivedCategory.Q.obj I) :
    ((RingedSite.derivedSheafHomBifunctor S.ambientSite).obj
          (op (S.siteModulePushforward.mapDerivedCategory.obj M))).obj K ≅
      S.siteModulePushforward.mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor S.closedSite).obj (op M)).obj
          (S.siteDerivedSheafHomExactSupport.obj K)) :=
  have ePush : S.siteModulePushforward.mapDerivedCategory.obj M ≅ DerivedCategory.Q.obj
      ((S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :=
    S.siteModulePushforward.mapDerivedCategory.mapIso eM ≪≫
      S.siteModulePushforward.mapDerivedCategoryFactors.app N
  have eEss : S.siteDerivedSheafHomExactSupport.obj K ≅ DerivedCategory.Q.obj
      ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    S.siteDerivedSheafHomExactSupport.mapIso eK ≪≫
      (S.derivedSheafHomExactSupportIsoOfIsKInjective I).symm
  ((RingedSite.derivedSheafHomBifunctor S.ambientSite).mapIso ePush.symm.op).app K ≪≫
    ((RingedSite.derivedSheafHomBifunctor S.ambientSite).obj (op (DerivedCategory.Q.obj
      ((S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))).mapIso eK ≪≫
    RingedSite.derivedSheafHomComparison S.ambientSite
      ((S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) I ≪≫
    (DerivedCategory.Q.mapIso (hom N I)).symm ≪≫
    (S.siteModulePushforward.mapDerivedCategoryFactors.app
      (RingedSite.sheafHomComplex S.closedSite N
        ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj).symm ≪≫
    S.siteModulePushforward.mapDerivedCategory.mapIso
      ((RingedSite.derivedSheafHomComparison S.closedSite N
          ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫
        ((RingedSite.derivedSheafHomBifunctor S.closedSite).obj
            (op (DerivedCategory.Q.obj N))).mapIso eEss.symm ≪≫
        ((RingedSite.derivedSheafHomBifunctor S.closedSite).mapIso eM.op).app
          (S.siteDerivedSheafHomExactSupport.obj K))

/-- **Stacks Project, Tag 0E2I.** For `M` in `D(𝒪_Z)` and `K` in `D(𝒪_X)`,

`R ℋom_{𝒪_X}(Ri_* M, K) ≅ Ri_* R ℋom_{𝒪_Z}(M, R ℰom(𝒪_Z, K))` in `D(𝒪_X)`,

granted the underived identification `hom` of internal Hom complexes. The representatives used
are the chosen K-injective models of `M` and `K`. -/
@[stacks 0E2I "the derived isomorphism, granted the underived internal Hom identification"]
def derivedSheafHomDerivedModulePushforwardIso
    (hom : ∀ (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O)) ℤ)
      (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O)) ℤ),
      (S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (RingedSite.sheafHomComplex S.closedSite N
            ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≅
        (RingedSite.sheafHomComplex S.ambientSite
          ((S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) I).obj)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O))) :
    ((RingedSite.derivedSheafHomBifunctor S.ambientSite).obj
          (op (S.siteModulePushforward.mapDerivedCategory.obj M))).obj K ≅
      S.siteModulePushforward.mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor S.closedSite).obj (op M)).obj
          (S.siteDerivedSheafHomExactSupport.obj K)) :=
  S.derivedSheafHomDerivedModulePushforwardIsoOfModels hom
    (RingedSite.kInjectiveModel S.closedSite M) (RingedSite.kInjectiveModel S.ambientSite K)
    (hI := RingedSite.isKInjective_kInjectiveModel S.ambientSite K)
    (RingedSite.kInjectiveModelIso S.closedSite M).symm
    (RingedSite.kInjectiveModelIso S.ambientSite K).symm

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
