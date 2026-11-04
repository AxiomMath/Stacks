module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology with support in a closed subscheme: the étale–Zariski comparison

Let `X` be a scheme, `Z ⊆ X` a closed subset with open complement `U`, and `F` a quasi-coherent
`𝒪_X`-module with associated module `F^a` on the small étale site of `X` (Stacks 03DU (4),
`AlgebraicGeometry.SmallEtale.associatedModule`).  Cohomology with support in `Z` is the right
derived functor of the functor of global sections vanishing on `U`.  This file supplies, on the
small étale site cut out of a big étale site, the ingredients of the comparison of the Zariski
and small étale versions of that derived functor at the coefficients `F` and `F^a`.

The comparison is the one of the source.  The small Zariski site of `X` sits inside its small
étale site as `AlgebraicGeometry.SmallEtale.opensToSmallEtale`; the direct image `ε_*` along the
resulting morphism of sites is restriction of an étale abelian sheaf to the opens of `X`, and
sections on the étale site over the image of an open are *literally* the sections of the
restriction over that open.  Consequently the étale functor of sections vanishing on `U` is
`ε_*` followed by its Zariski counterpart (`sectionsVanishingOutsidePushforward`).  Since `ε_*`
is left exact and carries injective abelian sheaves to injective abelian sheaves, a coefficient
whose higher direct images under `ε_*` vanish has its étale derived supported sections computed
by the Zariski ones (`rightDerivedCompIsoOfObjAcyclic`), and for `F^a` the direct image itself
is `F`, by Stacks 070S (2).

## Main definitions

* `Stacks.Sites.SupportedSections.sectionsVanishingOutside` — for a morphism `f : V ⟶ T` of a
  site, the functor sending an abelian sheaf to the sections over `T` whose restriction along
  `f` vanishes.  At the inclusion of the complement of a closed subset into the whole space this
  is the usual `Γ_Z`; on the small Zariski site of a ringed space it is the kernel of the same
  restriction map as `Stacks.Cohomology.SupportedComplexes.abelianSectionsWithSupport`.
* `AlgebraicGeometry.SmallEtale.zariskiRestrictionAb` and
  `AlgebraicGeometry.SmallEtale.zariskiExtensionAb` — the direct and inverse images of abelian
  sheaves along the inclusion of the small Zariski site of `X` into its small étale site.
* `AlgebraicGeometry.SmallEtale.etaleSectionsWithSupport` and
  `AlgebraicGeometry.SmallEtale.zariskiSectionsWithSupport` — the functors `Γ_Z` on the small
  étale and on the small Zariski site of `X`.
* `AlgebraicGeometry.SmallEtale.associatedAbelianSheaf` — the associated module `F^a` of
  Stacks 03DU (4), read as an abelian sheaf on the small étale site.

## Main results

* `Stacks.Sites.SupportedSections.sectionsVanishingOutsidePushforward` — the functor of sections
  vanishing outside a subobject is computed after direct image.
* `Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfObjAcyclic` — the right derived
  functors of a composite at a coefficient acyclic for the left factor.
* `AlgebraicGeometry.SmallEtale.zariskiRestrictionAb_preservesInjectiveObjects` — `ε_*` carries
  injective abelian sheaves to injective abelian sheaves.
* `AlgebraicGeometry.SmallEtale.associatedAbelianSheafRestrictionIso` — the direct image of
  `F^a` is the abelian sheaf underlying `F`, by Stacks 070S (2).

## Implementation notes

Stacks 0A46 itself is not stated here.  Clause (1) is
`AlgebraicGeometry.supportedCohomologyEtaleIso` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportEtaleZariski`, on Mathlib's
small étale site, where the vanishing of the higher direct images `R^nε_*(F^a)` for `n > 0`
(Stacks 03P2) is proved; clause (2) is
`AlgebraicGeometry.supportedCohomology_isQuasicoherent_and_associatedSheaf` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportQuasicoherent`.

The open `⊤` of `X`, read as an object of the small étale site, is a *final* object there —
this is `AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop` — so the sections over
it which `etaleSectionsWithSupport` cuts down are the global sections of `X_étale`, not sections
over some smaller object; the same holds for `⊤` on the small Zariski site.

Coefficients are `AddCommGrpCat.{u}` on both sites, the universe in which the associated module
of Stacks 03DU (4) takes its values.  Both sheaf categories are Grothendieck abelian, their
sites being essentially small, so both have enough injectives; those four facts are supplied
here as instances, as `AlgebraicGeometry.smallEtaleAbelianSheaf_enoughInjectives` does one
universe up in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupport`.

`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfObjAcyclic` is *not* a special case of
the neighbouring `Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`, and that one
does not apply here: it asks the left factor to be exact, whereas `ε_*` is right exact only
when every local ring of `X` is strictly henselian (Stacks 09AX,
`AlgebraicGeometry.zariskiPushforward_preservesFiniteColimits`).  What replaces exactness is
that `ε_*` preserves injective objects and that the single coefficient is `ε_*`-acyclic.

The functor `Stacks.Sites.SupportedSections.sectionsVanishingOutside` is stated for a general
site because it is used on two different ones here, and because the identification of the étale
functor with the composite is a statement about an arbitrary continuous functor.

## References

* [Stacks Project, Tag 0A46](https://stacks.math.columbia.edu/tag/0A46)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w v₁ v₂ u₁ u₂ u

namespace Stacks.Sites.SupportedSections

/-! ### Sections vanishing outside a subobject -/

section Generic

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- Restriction of sections along a morphism of a site, as a natural transformation between the
evaluation functors on abelian sheaves. -/
public abbrev sectionsRestriction {V T : C} (f : V ⟶ T) :
    (sheafSections J AddCommGrpCat.{w}).obj (op T) ⟶
      (sheafSections J AddCommGrpCat.{w}).obj (op V) :=
  (sheafSections J AddCommGrpCat.{w}).map f.op

/-- Sections of an abelian sheaf over `T` whose restriction along `f : V ⟶ T` vanishes.  For
`T` the whole space and `V` the open complement of a closed subset `Z` this is the functor
`Γ_Z` of global sections supported on `Z`. -/
@[sga "2 XIV 1.0" "more general"]
public def sectionsVanishingOutside {V T : C} (f : V ⟶ T) :
    Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  kernel (sectionsRestriction J f)

/-- Sections vanishing outside a subobject form an additive functor: the inclusion into the
sections over `T` is a pointwise monomorphism natural in the sheaf, and additivity of a map is
detected after composing with a monomorphism. -/
public instance sectionsVanishingOutside_additive {V T : C} (f : V ⟶ T) :
    (sectionsVanishingOutside.{w} J f).Additive := by
  change (kernel (sectionsRestriction.{w} J f)).Additive
  constructor
  intro A A' g g'
  apply (cancel_mono ((kernel.ι (sectionsRestriction.{w} J f)).app A')).1
  rw [(kernel.ι (sectionsRestriction.{w} J f)).naturality]
  simp

end Generic

/-- **Sections vanishing outside a subobject are computed after direct image.**  For a
continuous functor `G` between sites, sections of an abelian sheaf over `G.obj T` vanishing
along `G.map f` are the sections of its direct image over `T` vanishing along `f`: the direct
image is precomposition with `G.op`, so the two restriction maps are the same map, and
precomposition preserves the kernel computing either side. -/
public def sectionsVanishingOutsidePushforward {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K] {V T : C} (f : V ⟶ T) :
    G.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙ sectionsVanishingOutside.{w} J f ≅
      sectionsVanishingOutside.{w} K (G.map f) :=
  PreservesKernel.iso
      ((Functor.whiskeringLeft _ _ _).obj (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K))
      (sectionsRestriction.{w} J f) ≪≫
    kernelIsoOfEq (by ext M s; rfl)

end Stacks.Sites.SupportedSections

namespace Stacks.Cohomology.AcyclicCollapse

/-- **The right derived functors of a composite at a coefficient acyclic for the left factor.**
A left exact additive functor `G` that preserves injective objects carries an injective
resolution of an object `X` with `R^nG(X) = 0` for `n > 0` to an injective resolution of
`G(X)`, so the right derived functors of `G ⋙ T` at `X` are those of `T` at `G(X)`.

This is the collapse of the Grothendieck spectral sequence of the composite in the only case
needed: the whole `E_2`-page is concentrated in one row.  Unlike
`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic` it does not ask `G` to be
exact, only left exact; what replaces right exactness is the acyclicity of the single
coefficient `X`. -/
public def rightDerivedCompIsoOfObjAcyclic {A : Type u₁} {Bc : Type u₂} {E : Type*}
    [Category.{v₁} A] [Category.{v₂} Bc] [Category* E]
    [Abelian A] [Abelian Bc] [Abelian E]
    [HasInjectiveResolutions A] [HasInjectiveResolutions Bc]
    (G : A ⥤ Bc) [G.Additive] [PreservesFiniteLimits G] [G.PreservesInjectiveObjects]
    (T : Bc ⥤ E) [T.Additive] (X : A)
    (hX : ∀ n > 0, IsZero ((G.rightDerived n).obj X)) (n : ℕ) :
    ((G ⋙ T).rightDerived n).obj X ≅ (T.rightDerived n).obj (G.obj X) := by
  let I := injectiveResolution X
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let ι : (CochainComplex.single₀ Bc).obj (G.obj X) ⟶ K :=
    (CochainComplex.fromSingle₀Equiv K (G.obj X)).symm
      ⟨G.map (I.ι.f 0), by
        change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
        rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]⟩
  have hc : HomologicalComplex.cyclesMap ι 0 =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (G.obj X)).hom ≫
        I.toRightDerivedZero' G := by
    apply (cancel_mono (K.iCycles 0)).1
    simp only [HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
    change _ = _ ≫ _ ≫ I.toRightDerivedZero' G ≫
      ((G.mapHomologicalComplex _).obj I.cocomplex).iCycles 0
    rw [I.toRightDerivedZero'_comp_iCycles G]
    simp [ι, CochainComplex.fromSingle₀Equiv, HomologicalComplex.singleObjXSelf]
  have : QuasiIso ι := by
    rw [quasiIso_iff]
    intro q
    cases q with
    | zero =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      have : IsIso (HomologicalComplex.cyclesMap ι 0) := by rw [hc]; infer_instance
      exact IsIso.of_isIso_fac_left (HomologicalComplex.homologyπ_naturality ι 0)
    | succ q =>
      rw [quasiIsoAt_iff_exactAt ι (q + 1) (CochainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact (hX (q + 1) (Nat.succ_pos q)).of_iso (I.isoRightDerivedObj G (q + 1)).symm
  let Jr : InjectiveResolution (G.obj X) :=
    { cocomplex := K
      injective := fun q => G.injective_obj (I.cocomplex.X q)
      ι := ι }
  exact I.isoRightDerivedObj (G ⋙ T) n ≪≫
    (HomologicalComplex.homologyFunctor E _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ T)) _).app I.cocomplex).symm ≪≫
    (Jr.isoRightDerivedObj T n).symm

end Stacks.Cohomology.AcyclicCollapse

namespace AlgebraicGeometry.SmallEtale

/-! ### Enough injectives on the two sites -/

/-- Abelian sheaves on the small Zariski site of a scheme form a Grothendieck abelian category,
the site of opens being small. -/
public instance isGrothendieckAbelian_opens_ab (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Abelian sheaves on the small étale site of a scheme form a Grothendieck abelian category,
the site being essentially small in the universe of the schemes. -/
public instance isGrothendieckAbelian_smallEtale_ab (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) :
    IsGrothendieckAbelian.{u} (Sheaf (topology B X hX) AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Abelian sheaves on the small Zariski site of a scheme have enough injectives, being a
Grothendieck abelian category. -/
public instance enoughInjectives_opens_ab (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

/-- Abelian sheaves on the small étale site of a scheme have enough injectives, being a
Grothendieck abelian category. -/
public instance enoughInjectives_smallEtale_ab (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) :
    EnoughInjectives (Sheaf (topology B X hX) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-! ### The direct image along the inclusion of the small Zariski site -/

/-- The direct image `ε_*` of abelian sheaves along the inclusion of the small Zariski site of
`X` into its small étale site: restriction of an étale abelian sheaf to the open subschemes. -/
public abbrev zariskiRestrictionAb :
    Sheaf (topology B X hX) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} :=
  (opensToSmallEtale B X hX).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥X) (topology B X hX)

/-- The direct image `ε_*` is additive: on sections it is the identity. -/
public instance zariskiRestrictionAb_additive : (zariskiRestrictionAb B X hX).Additive where
  map_add := by intros; rfl

/-- The inverse image `ε^{-1}` of abelian sheaves along the inclusion of the small Zariski site
of `X` into its small étale site. -/
public abbrev zariskiExtensionAb :
    Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} ⥤
      Sheaf (topology B X hX) AddCommGrpCat.{u} :=
  (opensToSmallEtale B X hX).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥X) (topology B X hX)

/-- The inverse image is left adjoint to the direct image, the inclusion of the small Zariski
site being continuous. -/
public abbrev zariskiExtensionAdjunction :
    zariskiExtensionAb B X hX ⊣ zariskiRestrictionAb B X hX :=
  (opensToSmallEtale B X hX).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥X) (topology B X hX)

/-- **The inverse image `ε^{-1}` is left exact.**  The presheaf inverse image is the left Kan
extension along the inclusion of the small Zariski site, computed pointwise by a colimit over a
costructured-arrow category; representable flatness of the inclusion
(`AlgebraicGeometry.SmallEtale.representablyFlat_opensToSmallEtale`) makes that category
filtered, the forgetful functor of abelian groups preserves filtered colimits of that size, and
sheafification is left exact. -/
public instance zariskiExtensionAb_preservesFiniteLimits :
    PreservesFiniteLimits (zariskiExtensionAb B X hX) := by
  have hfor : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, u, u} _
  have hlan := Stacks.Topology.lan_preservesFiniteLimits_of_flat
    (E := AddCommGrpCat.{u}) (F := opensToSmallEtale B X hX) (hPres := fun V => by
      have hfilt : IsFiltered (CostructuredArrow (opensToSmallEtale B X hX).op V) :=
        IsFiltered.of_equivalence
          (structuredArrowOpEquivalence (opensToSmallEtale B X hX) V.unop)
      exact hfor.preserves_filtered_colimits
        (CostructuredArrow (opensToSmallEtale B X hX).op V))
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- The inverse image `ε^{-1}` preserves monomorphisms, being left exact. -/
public instance zariskiExtensionAb_preservesMonomorphisms :
    (zariskiExtensionAb B X hX).PreservesMonomorphisms := by
  constructor
  intro A A' g _
  exact preserves_mono_of_preservesLimit _ g

/-- **The direct image `ε_*` carries injective abelian sheaves to injective abelian sheaves**:
it is right adjoint to the left exact inverse image. -/
public instance zariskiRestrictionAb_preservesInjectiveObjects :
    (zariskiRestrictionAb B X hX).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (zariskiExtensionAdjunction B X hX)

/-- The direct image `ε_*` is left exact, being a right adjoint. -/
public instance zariskiRestrictionAb_preservesFiniteLimits :
    PreservesFiniteLimits (zariskiRestrictionAb B X hX) :=
  haveI : (zariskiRestrictionAb B X hX).IsRightAdjoint :=
    (zariskiExtensionAdjunction B X hX).isRightAdjoint
  inferInstance

/-! ### The two functors of sections with support -/

variable (Z : Set ↥X) (hZ : IsClosed Z)

/-- The open complement of a closed subset of a scheme. -/
public abbrev openComplementOpens : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The inclusion of the open complement of a closed subset into the whole scheme, as a
morphism of the small Zariski site. -/
public abbrev openComplementι : openComplementOpens X Z hZ ⟶ (⊤ : X.Opens) :=
  homOfLE (le_top : openComplementOpens X Z hZ ≤ ⊤)

/-- `Γ_Z` on the small Zariski site of `X`: global sections of an abelian sheaf whose
restriction to the open complement of `Z` vanishes. -/
public abbrev zariskiSectionsWithSupport :
    Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Stacks.Sites.SupportedSections.sectionsVanishingOutside.{u}
    (Opens.grothendieckTopology ↥X) (openComplementι X Z hZ)

/-- `Γ_Z` on the small étale site of `X`: sections of an abelian sheaf over `X` whose
restriction to the open complement of `Z`, read as an object of the small étale site,
vanishes. -/
public abbrev etaleSectionsWithSupport :
    Sheaf (topology B X hX) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Stacks.Sites.SupportedSections.sectionsVanishingOutside.{u} (topology B X hX)
    ((opensToSmallEtale B X hX).map (openComplementι X Z hZ))

/-- **The étale functor of sections supported on `Z` is the direct image followed by the Zariski
one.**  Sections on the small étale site over the image of an open of `X` are the sections of
the restriction over that open, and the restriction maps to the complement of `Z` agree. -/
public def etaleSectionsWithSupportIso :
    zariskiRestrictionAb B X hX ⋙ zariskiSectionsWithSupport X Z hZ ≅
      etaleSectionsWithSupport B X hX Z hZ :=
  Stacks.Sites.SupportedSections.sectionsVanishingOutsidePushforward.{u}
    (Opens.grothendieckTopology ↥X) (topology B X hX) (opensToSmallEtale B X hX)
    (openComplementι X Z hZ)

/-! ### The associated module as an abelian sheaf, and its direct image -/

variable (F : X.Modules) [F.IsQuasicoherent]

/-- The associated module `F^a` of Stacks 03DU (4) at `τ = étale`, read as an abelian sheaf on
the small étale site of `X`.  This is the coefficient at which Stacks 0A46 states the
comparison. -/
public abbrev associatedAbelianSheaf : Sheaf (topology B X hX) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (structureSheaf B X hX)).obj ((associatedModule B X hX).obj F)

/-- **The direct image of `F^a` is the abelian sheaf underlying `F`.**  The unit of the
associated-module adjunction of the small étale site is an isomorphism at a quasi-coherent
module, which is `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, the small-étale form of
Stacks 070S (2); forgetting the module structure turns it into this isomorphism of abelian
sheaves, direct image of abelian sheaves and restriction of modules along the inclusion of the
small Zariski site having the same underlying presheaf. -/
public def associatedAbelianSheafRestrictionIso :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj F ≅
      (zariskiRestrictionAb B X hX).obj (associatedAbelianSheaf B X hX F) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).mapIso
    (@asIso _ _ _ _ _ (unitIsoOnQuasicoherent B X hX ⟨F, inferInstance⟩))

end AlgebraicGeometry.SmallEtale

end
