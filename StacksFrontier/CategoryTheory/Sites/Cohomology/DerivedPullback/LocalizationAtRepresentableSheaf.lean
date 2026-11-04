module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.DerivedIsomorphismLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.PullbackAlongAMorphismOfRingedTopoi
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# Derived pullback to the localization of a ringed site at a representable sheaf

Let `(𝒞, 𝒪)` be a ringed site, `V` an object of `𝒞` and `h_V^#` the sheaf associated to the
presheaf represented by `V`. Localizing the ringed topos at `h_V^#` ([Stacks, Tag 04IE]) gives a
morphism of ringed topoi `j : (Sh(𝒞)/h_V^#, 𝒪_V) ⟶ (Sh(𝒞), 𝒪)`, whose pullback of sheaves of
modules is exact; by [Stacks, Tag 04J3] the localized topos is the slice topos `Sh(𝒞/V)`, and
the restriction of sheaves of modules to the slice site factors through `j^*`. This file draws
the two consequences that the proof of [Stacks, Tag 0944] needs to pass from the slice sites,
on which perfectness ([Stacks, Tag 08G5]) is defined, to the localized ringed topoi, on which the
projection formula map is compared with base change:

* the derived pullbacks to the localizations at `h_{V_k}^#`, for a family of objects `V_k`
  covering the final object, are jointly conservative on `D(𝒪)`;
* if the restriction of a complex `E` to `𝒞/V` receives a quasi-isomorphism from a strictly
  perfect complex, then the derived pullback of `E` to the localization at `h_V^#` is
  represented by a strictly perfect complex.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackIsoMapDerivedCategory`: along a
  morphism of ringed topoi whose pullback of modules is exact, the derived pullback is the functor
  that pullback induces on derived categories.
* `AlgebraicGeometry.RingedSite.overFunctorIsoPullbackLocalization`: restriction to `𝒞/V` is the
  pullback to the localization at `h_V^#` followed by the pullback along the identification of
  [Stacks, Tag 04J3].
* `AlgebraicGeometry.RingedSite.representableLocalizationInverse`: the inverse of that
  identification, as a morphism of ringed topoi.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_of_isIso_derivedPullback_localizationMorphism`: joint
  conservativity.
* `AlgebraicGeometry.RingedSite.exists_isStrictlyPerfect_derivedPullback_localizationMorphism`:
  transport of strictly perfect models.

## Implementation notes

The localized ringed topos is read with the ringed topos `X.ringedTopos` of the ringed site
throughout, and so are the objects of `D(𝒪)`: mixing that spelling with the one of the ringed site
itself makes the homology functors and the categories of modules involved differ by instance
terms, which the elaborator cannot reconcile in reasonable time.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (h : RingedToposHom X Y) [PreservesFiniteLimits h.toModulesHom.pullbackModules]
  [(pullbackOnHomotopy h).HasLeftDerivedFunctor quasiIsoTarget]

/-- **Along a morphism of ringed topoi whose pullback of modules is exact, the derived pullback
is the functor that pullback induces on derived categories.** -/
def derivedPullbackIsoMapDerivedCategory :
    haveI := h.pullbackModules_preservesFiniteColimits
    derivedPullback h ≅ (h.toModulesHom.pullbackModules).mapDerivedCategory :=
  haveI := h.pullbackModules_preservesFiniteColimits
  haveI : (h.toModulesHom.pullbackModules).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (h.toModulesHom.pullbackModules).mapDerivedCategory.IsLeftDerivedFunctor
      (Functor.mapDerivedCategoryFactorsh (h.toModulesHom.pullbackModules)).hom quasiIsoTarget :=
    Functor.isLeftDerivedFunctor_of_inverts quasiIsoTarget _
      (Functor.mapDerivedCategoryFactorsh (h.toModulesHom.pullbackModules))
  Functor.leftDerivedUnique (h.toModulesHom.pullbackModules).mapDerivedCategory
    (derivedPullback h) (derivedPullbackComparison h)
    (Functor.mapDerivedCategoryFactorsh (h.toModulesHom.pullbackModules)).hom quasiIsoTarget

end Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)]

/-- Restriction of sheaves of modules to the slice site over `V` is the pullback to the
localization of the ringed topos at `h_V^#`, followed by the pullback along the identification
of Stacks 04J3 of the slice topos with that localization. -/
noncomputable def overFunctorIsoPullbackLocalization (V : X.C) :
    SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V ≅
      (X.ringedTopos.localizationMorphism (representableSheaf X V)).toModulesHom.pullbackModules ⋙
        (representableLocalizationRingedMorphism X V).toModulesHom.pullbackModules :=
  (localizationPullbackToposIsoRestriction X V).symm ≪≫
    (localizationTwoIso X V).pullbackModulesIso.symm ≪≫
    RingedToposHom.pullbackModulesCompIso (representableLocalizationRingedMorphism X V)
      (X.ringedTopos.localizationMorphism (representableSheaf X V))

/-- The structure map of the localization at a sheaf is invertible. -/
instance isIso_localizationMorphism_fSharpInverseImage (G : X.ringedTopos.Topos) :
    IsIso (X.ringedTopos.localizationMorphism G).fSharpInverseImage := by
  rw [RingedTopos.localization_fSharp_inverseImage]
  exact Iso.isIso_hom _

/-- The structure map of the identification of Stacks 04J3 is invertible. -/
instance isIso_representableLocalizationRingedMorphism_fSharpInverseImage (V : X.C) :
    IsIso (representableLocalizationRingedMorphism X V).fSharpInverseImage := by
  rw [representableLocalizationRingedMorphism_fSharpInverseImage]
  exact Iso.isIso_hom _

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
  Stacks.Cohomology.Localization.additive_overFunctor

/-- Pullback of sheaves of modules along a morphism of ringed topoi is additive. -/
theorem _root_.AlgebraicGeometry.RingedToposHom.additive_pullbackModules
    {Z W : RingedTopos.{u, u, u}}
    [Z.J.HasSheafCompose (forget RingCat.{u})] [W.J.HasSheafCompose (forget RingCat.{u})]
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [W.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (h : RingedToposHom Z W) : h.toModulesHom.pullbackModules.Additive :=
  (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    h.toModulesHom).left_adjoint_additive

/-- Pullback of modules to the localization at a sheaf is additive. -/
instance additive_localizationMorphism_pullbackModules (G : X.ringedTopos.Topos) :
    (X.ringedTopos.localizationMorphism G).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.additive_pullbackModules _

/-- Pullback of modules to the localization at a sheaf is left exact. -/
instance preservesFiniteLimits_localizationMorphism_pullbackModules (G : X.ringedTopos.Topos) :
    PreservesFiniteLimits (X.ringedTopos.localizationMorphism G).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp _

/-- Pullback of modules to the localization at a sheaf is right exact. -/
instance preservesFiniteColimits_localizationMorphism_pullbackModules (G : X.ringedTopos.Topos) :
    PreservesFiniteColimits (X.ringedTopos.localizationMorphism G).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModules_preservesFiniteColimits _

/-- Pullback of modules along the identification of Stacks 04J3 is additive. -/
instance additive_representableLocalizationRingedMorphism_pullbackModules (V : X.C) :
    (representableLocalizationRingedMorphism X V).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.additive_pullbackModules _

/-- Pullback of modules along the identification of Stacks 04J3 is left exact. -/
instance preservesFiniteLimits_representableLocalizationRingedMorphism_pullbackModules (V : X.C) :
    PreservesFiniteLimits
      (representableLocalizationRingedMorphism X V).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp _

/-- Pullback of modules along the identification of Stacks 04J3 is right exact. -/
instance preservesFiniteColimits_representableLocalizationRingedMorphism_pullbackModules (V : X.C) :
    PreservesFiniteColimits
      (representableLocalizationRingedMorphism X V).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModules_preservesFiniteColimits _

/-- The derived pullback along a localization morphism exists. -/
instance hasLeftDerivedFunctor_localizationMorphism (G : X.ringedTopos.Topos) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy
      (X.ringedTopos.localizationMorphism G)).HasLeftDerivedFunctor
      Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X.ringedTopos.localizationMorphism G)


/-- A morphism of sheaves of `𝒪`-modules whose pullback to the localization at `h_V^#` is
invertible restricts to an invertible morphism on the slice site over `V`. -/
theorem isIso_over_of_isIso_localizationMorphism_pullbackModules_map (V : X.C)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (ψ : M ⟶ N)
    [IsIso ((X.ringedTopos.localizationMorphism
      (representableSheaf X V)).toModulesHom.pullbackModules.map ψ)] :
    IsIso (ψ.over V) := by
  have h : IsIso ((representableLocalizationRingedMorphism X V).toModulesHom.pullbackModules.map
      ((X.ringedTopos.localizationMorphism
        (representableSheaf X V)).toModulesHom.pullbackModules.map ψ)) :=
    inferInstance
  exact (NatIso.isIso_map_iff (overFunctorIsoPullbackLocalization X V) ψ).2 h

/-- The pullbacks of sheaves of `𝒪`-modules to the localizations at the sheaves `h_{V_k}^#` of a
family of objects covering the final object are jointly conservative. -/
theorem isIso_of_isIso_localizationMorphism_pullbackModules_map {ι : Type*} (V : ι → X.C)
    (hV : X.J.CoversTop V)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (ψ : M ⟶ N)
    (h : ∀ k, IsIso ((X.ringedTopos.localizationMorphism
      (representableSheaf X (V k))).toModulesHom.pullbackModules.map ψ)) :
    IsIso ψ :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV ψ fun k =>
    have := h k
    isIso_over_of_isIso_localizationMorphism_pullbackModules_map X (V k) ψ

/-- **The localizations at the sheaves `h_V^#` of a family of objects covering the final object
are jointly conservative on `D(𝒪)`.** A morphism of `D(𝒪)` whose derived pullbacks to all the
localizations `Sh(𝒞)/h_{V_k}^#` are invertible is invertible: on cohomology sheaves the
derived pullback is the pullback of modules (which is exact), and the restriction to the slice
site over `V_k` factors through it (Stacks 04J3), so invertibility follows from its locality on
the site. -/
theorem isIso_of_isIso_derivedPullback_localizationMorphism {ι : Type*} (V : ι → X.C)
    (hV : X.J.CoversTop V)
    {A B : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O))}
    (φ : A ⟶ B)
    (h : ∀ k, IsIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
      (X.ringedTopos.localizationMorphism (representableSheaf X (V k)))).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_localizationMorphism_pullbackModules_map X V hV _ fun k => ?_
  have hk := h k
  have h₁ : IsIso ((X.ringedTopos.localizationMorphism
      (representableSheaf X (V k))).toModulesHom.pullbackModules.mapDerivedCategory.map φ) :=
    (NatIso.isIso_map_iff
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackIsoMapDerivedCategory
        (X.ringedTopos.localizationMorphism (representableSheaf X (V k)))) φ).1 hk
  have h₂ := (NatIso.isIso_map_iff (Functor.mapDerivedCategoryHomologyIso
      (X.ringedTopos.localizationMorphism (representableSheaf X (V k))).toModulesHom.pullbackModules
        n) φ).1 (Functor.map_isIso (DerivedCategory.homologyFunctor _ n) _)
  exact h₂


/-- The direct image of the identification of Stacks 04J3 of the slice topos with the
localization at `h_V^#` is an equivalence. -/
instance isEquivalence_representableLocalizationRingedMorphism_pushforward (V : X.C) :
    (representableLocalizationRingedMorphism X V).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs (representableLocalizationEquivalence X V).functor.IsEquivalence

/-- The structure map of a morphism of ringed topoi whose direct image is an equivalence is
invertible as soon as its inverse-image form is. -/
theorem _root_.AlgebraicGeometry.RingedToposHom.isIso_fSharp_of_isIso_fSharpInverseImage
    {Z W : RingedTopos.{u, u, u}}
    [Z.J.HasSheafCompose (forget RingCat.{u})] [W.J.HasSheafCompose (forget RingCat.{u})]
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [W.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (h : RingedToposHom Z W) [h.toToposHom.pushforward.IsEquivalence]
    [IsIso h.fSharpInverseImage] : IsIso h.fSharp := by
  suffices IsIso (W.forgetRing.map h.fSharp) from isIso_of_reflects_iso h.fSharp W.forgetRing
  have key : h.toToposHom.adj.unit.app (W.forgetRing.obj W.O) ≫
      h.toToposHom.pushforward.map (Z.forgetRing.map h.fSharpInverseImage) =
      W.forgetRing.map h.fSharp := by
    rw [RingedToposHom.fSharpInverseImage_forget_homEquiv]
    exact (h.toToposHom.adj.homEquiv_unit (W.forgetRing.obj W.O)
        (Z.forgetRing.obj Z.O) _).symm.trans
      ((h.toToposHom.adj.homEquiv (W.forgetRing.obj W.O)
        (Z.forgetRing.obj Z.O)).apply_symm_apply (W.forgetRing.map h.fSharp))
  rw [← key]
  have h1 : IsIso (h.toToposHom.adj.unit.app (W.forgetRing.obj W.O)) := inferInstance
  have h0 : IsIso (Z.forgetRing.map h.fSharpInverseImage) :=
    Functor.map_isIso Z.forgetRing h.fSharpInverseImage
  have h2 : IsIso (h.toToposHom.pushforward.map (Z.forgetRing.map h.fSharpInverseImage)) :=
    Functor.map_isIso _ (Z.forgetRing.map h.fSharpInverseImage)
  exact IsIso.comp_isIso' h1 h2

/-- The direct-image structure map of the identification of Stacks 04J3 is invertible. -/
instance isIso_representableLocalizationRingedMorphism_fSharp (V : X.C) :
    IsIso (representableLocalizationRingedMorphism X V).fSharp :=
  RingedToposHom.isIso_fSharp_of_isIso_fSharpInverseImage _


/-- The inverse of the identification of Stacks 04J3 of the slice topos over `V` with the
localization at `h_V^#`, as a morphism of ringed topoi. -/
noncomputable abbrev representableLocalizationInverse (V : X.C) :
    RingedToposHom (X.ringedTopos.localizedRingedTopos (representableSheaf X V))
      (X.over V).ringedTopos :=
  RingedToposHom.inverse (X := (X.over V).ringedTopos)
    (Y := X.ringedTopos.localizedRingedTopos (representableSheaf X V))
    (representableLocalizationRingedMorphism X V)

/-- The direct image of the inverse identification is an equivalence. -/
instance isEquivalence_representableLocalizationInverse_pushforward (V : X.C) :
    (representableLocalizationInverse X V).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs
    (representableLocalizationRingedMorphism X V).toToposHom.inverseImage.IsEquivalence

/-- The structure map of the inverse identification is invertible. -/
instance isIso_representableLocalizationInverse_fSharp (V : X.C) :
    IsIso (representableLocalizationInverse X V).fSharp := by
  show IsIso (inv (representableLocalizationRingedMorphism X V).fSharpInverseImage)
  infer_instance

/-- The inverse-image structure map of the inverse identification is invertible. -/
instance isIso_representableLocalizationInverse_fSharpInverseImage (V : X.C) :
    IsIso (representableLocalizationInverse X V).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage _

/-- Pullback of modules along the inverse identification is additive. -/
instance additive_representableLocalizationInverse_pullbackModules (V : X.C) :
    (representableLocalizationInverse X V).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.additive_pullbackModules _

/-- Pullback of modules along the inverse identification is left exact. -/
instance preservesFiniteLimits_representableLocalizationInverse_pullbackModules (V : X.C) :
    PreservesFiniteLimits (representableLocalizationInverse X V).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp _

/-- Pullback of modules along the inverse identification is right exact. -/
instance preservesFiniteColimits_representableLocalizationInverse_pullbackModules (V : X.C) :
    PreservesFiniteColimits (representableLocalizationInverse X V).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModules_preservesFiniteColimits _

/-- Pulling back to the slice topos over `V` and then back along the inverse of the
identification of Stacks 04J3 returns the module. -/
noncomputable def pullbackCompRepresentableLocalizationInverseIso (V : X.C) :
    (representableLocalizationRingedMorphism X V).toModulesHom.pullbackModules ⋙
        (representableLocalizationInverse X V).toModulesHom.pullbackModules ≅ 𝟭 _ :=
  (RingedToposHom.pullbackModulesCompIso (representableLocalizationInverse X V)
      (representableLocalizationRingedMorphism X V)).symm ≪≫
    RingedToposHom.pullbackModulesCompInverseIso (representableLocalizationRingedMorphism X V)

/-- Restriction to the slice site over `V` followed by the pullback along the inverse of the
identification of Stacks 04J3 is the pullback to the localization at `h_V^#`. -/
noncomputable def overFunctorCompRepresentableLocalizationInverseIso (V : X.C) :
    SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V ⋙
        (representableLocalizationInverse X V).toModulesHom.pullbackModules ≅
      (X.ringedTopos.localizationMorphism (representableSheaf X V)).toModulesHom.pullbackModules :=
  Functor.isoWhiskerRight (overFunctorIsoPullbackLocalization X V)
      (representableLocalizationInverse X V).toModulesHom.pullbackModules ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pullbackCompRepresentableLocalizationInverseIso X V) ≪≫
    Functor.rightUnitor _

/-- **A strictly perfect model over the slice site gives a strictly perfect model on the
localization.** If the restriction of a complex `E₀` of `𝒪`-modules to the slice site over `V`
receives a quasi-isomorphism from a strictly perfect complex `P`, then the derived pullback of
`E₀` to the localization of the ringed topos at `h_V^#` is represented by a strictly perfect
complex, namely the pullback of `P` along the inverse of the identification of Stacks 04J3. -/
theorem exists_isStrictlyPerfect_derivedPullback_localizationMorphism (V : X.C)
    (E₀ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)) ℤ)
    (P : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (q : P ⟶ X.restrictComplex E₀ V) [QuasiIso q] :
    ∃ P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (X.ringedTopos.localizedRingedTopos (representableSheaf X V)).O)) ℤ,
      IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
          (X.ringedTopos.localizedRingedTopos (representableSheaf X V)).O) P' ∧
        Nonempty ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
          (X.ringedTopos.localizationMorphism (representableSheaf X V))).obj
            (DerivedCategory.Q.obj E₀) ≅ DerivedCategory.Q.obj P') := by
  let F := (representableLocalizationInverse X V).toModulesHom.pullbackModules
  let j :=
    (X.ringedTopos.localizationMorphism (representableSheaf X V)).toModulesHom.pullbackModules
  let P₁ : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).ringedTopos.O)) ℤ := P
  let R₁ : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).ringedTopos.O)) ℤ := X.restrictComplex E₀ V
  let q₁ : P₁ ⟶ R₁ := q
  have hq₁ : QuasiIso q₁ := ‹QuasiIso q›
  have hq : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q₁) := inferInstance
  let e := overFunctorCompRepresentableLocalizationInverseIso X V
  let c : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R₁ ≅
      (j.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀ :=
    HomologicalComplex.Hom.isoOfComponents (fun n => e.app (E₀.X n))
      (fun a b _ => (e.hom.naturality (E₀.d a b)).symm)
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₁,
    RingedToposHom.isStrictlyPerfect_pullbackModules (representableLocalizationInverse X V) hP,
    ⟨?_⟩⟩
  exact (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackIsoMapDerivedCategory
      (X.ringedTopos.localizationMorphism (representableSheaf X V))).app _ ≪≫
    j.mapDerivedCategoryFactors.app E₀ ≪≫
    DerivedCategory.Q.mapIso c.symm ≪≫
    (asIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q₁))).symm

end AlgebraicGeometry.RingedSite

end
