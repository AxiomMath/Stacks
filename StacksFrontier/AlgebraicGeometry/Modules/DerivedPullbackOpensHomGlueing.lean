module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfDerivedHoms
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.FullnessOfExtensionByZeroDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsFromTheCoverUnconditional

/-!
# Glueing morphisms along derived pullbacks to opens

Let `X` be a scheme, `ℬ` a collection of opens covering `X` such that the intersection of two
members is the union of the members it contains, and `K`, `L` objects of `D(𝒪_X)` with
`Ext^n(K|_U, L|_U) = 0` for `n < 0` and `U ∈ ℬ`, where `K|_U` is the derived pullback along the
open immersion `U ⟶ X`. Then a family of morphisms `K|_U ⟶ L|_U` compatible with restriction
along the inclusions `V ⟶ U` of members comes from a unique morphism `K ⟶ L`
(Stacks 0D66 (2)), restriction from `U` to `V` being derived pullback along `V ⟶ U` read through
the comparison `resComp` of Stacks 0D5S.

## Main definitions

* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.resComp`: the identification
  `(V ⟶ U)^*(U ⟶ X)^* K ≅ (V ⟶ X)^* K`, natural in `K` (`resComp_hom_naturality`).

## Main results

* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.existsUnique_hom_of_derivedPullback_opens`:
  the glueing statement above.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open ExtensionByZeroModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! Instances on the slices of a ringed site. -/

/-- Sheaves of abelian groups on the slice site over `V` admit sheafification. -/
local instance hasSheafifyOverSite (𝒳 : AlgebraicGeometry.RingedSite.{u, u, u}) (V : 𝒳.C) :
    HasSheafify (𝒳.J.over V) AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat (𝒳.J.over V)

/-- On the slice site over `V`, the morphisms of presheaves of abelian groups inverted by
sheafification are the locally bijective ones. -/
local instance wEqualsLocallyBijectiveOverSite (𝒳 : AlgebraicGeometry.RingedSite.{u, u, u})
    (V : 𝒳.C) :
    (𝒳.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (𝒳.J.over V)

/-- Restriction of sheaves of modules along a morphism `W ⟶ V` of slices is additive. -/
local instance additiveOverMapSite (𝒳 : AlgebraicGeometry.RingedSite.{u, u, u}) {V W : 𝒳.C}
    (g : W ⟶ V) :
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒳.O) g).Additive :=
  inferInstanceAs (SheafOfModules.pushforward.{u}
    ((Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf 𝒳.O) g).inv)).Additive

/-- Restriction of sheaves of modules along a morphism `W ⟶ V` of slices preserves finite
limits. -/
local instance preservesFiniteLimitsOverMapSite (𝒳 : AlgebraicGeometry.RingedSite.{u, u, u})
    {V W : 𝒳.C}
    (g : W ⟶ V) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒳.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction of sheaves of modules along a morphism `W ⟶ V` of slices preserves finite
colimits. -/
local instance preservesFiniteColimitsOverMapSite (𝒳 : AlgebraicGeometry.RingedSite.{u, u, u})
    {V W : 𝒳.C}
    (g : W ⟶ V) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒳.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

namespace AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing

variable {X : Scheme.{u}}

/-- Restriction to the slice site over `U`, on derived categories. -/
abbrev sliceRes (U : X.Opens) :=
  (SheafOfModules.overFunctor.{u} (structureSheafRing X.toRingedSpace) U).mapDerivedCategory

/-- Passage from the slice model to the open-subspace model, on derived categories. -/
abbrev toSubspace (U : X.Opens) :=
  (Stacks.DerivedGlueing.sliceToSubspace (structureSheafRing X.toRingedSpace) U).mapDerivedCategory

/-- The derived equivalence between the slice and open-subspace models over `U`. -/
def sliceSubspaceEquivalence (U : X.Opens) :=
  Stacks.DerivedGlueing.mapDerivedCategoryEquivalence
    (Stacks.DerivedGlueing.sliceToSubspace (structureSheafRing X.toRingedSpace) U)
    (Stacks.DerivedGlueing.subspaceToSlice (structureSheafRing X.toRingedSpace) U)
    (U.sheafOfModulesEquivOver (structureSheafRing X.toRingedSpace)).unitIso
    (U.sheafOfModulesEquivOver (structureSheafRing X.toRingedSpace)).counitIso

/-- Restriction to `U` in the open-subspace model. -/
abbrev jStarDerived (U : X.Opens) :=
  (jStar U (structureSheafRing X.toRingedSpace)).mapDerivedCategory

/-- The morphism property at which restriction to the slice over `U` is a localization. -/
abbrev sliceW (U : X.Opens) : MorphismProperty (DerivedCategory X.Modules) :=
  (MorphismProperty.isomorphisms _).inverseImage (jStarDerived U)

/-- Restriction to an open is a localization functor on derived categories. -/
theorem jStarDerived_isLocalization (U : X.Opens) :
    (jStarDerived U).IsLocalization (sliceW U) := by
  have hff := Stacks.DerivedGlueing.fullyFaithful_jShriek_mapDerivedCategory
    (structureSheafRing X.toRingedSpace) U
  have := hff.full
  have := hff.faithful
  exact (Adjunction.mapDerivedCategory
    (jShriekAdjunction U (structureSheafRing X.toRingedSpace))).isLocalization'

/-- `j^*` is restriction to the slice followed by passage to the open-subspace model. -/
def jStarDerivedIso (U : X.Opens) : jStarDerived U ≅ sliceRes U ⋙ toSubspace U :=
  (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (structureSheafRing X.toRingedSpace) U)
      (Stacks.DerivedGlueing.sliceToSubspace (structureSheafRing X.toRingedSpace) U)).symm

/-- **Restriction to the slice over an open is a localization functor** on derived categories. -/
theorem sliceRes_isLocalization (U : X.Opens) : (sliceRes U).IsLocalization (sliceW U) := by
  have := jStarDerived_isLocalization U
  exact Functor.IsLocalization.of_equivalence_target (jStarDerived U) (sliceW U) (sliceRes U)
    (sliceSubspaceEquivalence U).symm
    (Functor.isoWhiskerRight (jStarDerivedIso U) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (sliceRes U) (sliceSubspaceEquivalence U).unitIso.symm ≪≫
      Functor.rightUnitor _)

/-- The derived pullback along `U ⟶ X` is restriction to the slice over `U` followed by
passage to the open-subspace model. -/
def sliceIso (U : X.Opens) :
    sliceRes U ⋙ toSubspace U ≅ derivedPullback U.ι.toLRSHom.toShHom :=
  Stacks.SheafOfModules.derivedOverFunctorEquiv U ≪≫
    Scheme.Modules.derivedRestrictIsoDerivedPullback U.ι

/-- Derived pullback along equal morphisms of schemes is natural in the object. -/
theorem derivedPullbackCongrObj_hom_naturality {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (h : a = b)
    {K L : DerivedCategory Z.Modules} (χ : K ⟶ L) :
    (derivedPullback a.toLRSHom.toShHom).map χ ≫ (Scheme.derivedPullbackCongrObj h L).hom =
      (Scheme.derivedPullbackCongrObj h K).hom ≫ (derivedPullback b.toLRSHom.toShHom).map χ := by
  subst h
  simp [Scheme.derivedPullbackCongrObj]

variable {U V : X.Opens} (hVU : V ≤ U)

/-- Derived pullback along the inclusion `V ⟶ U` of opens of `X`. -/
abbrev pullbackLE := derivedPullback (X.homOfLE hVU).toLRSHom.toShHom

/-- **Restricting to `U` and then to `V` is restricting to `V`**: the composite of the derived
pullbacks along `V ⟶ U` and `U ⟶ X` is the derived pullback along `V ⟶ X`. -/
def resComp (K : DerivedCategory X.Modules) :
    (pullbackLE hVU).obj ((derivedPullback U.ι.toLRSHom.toShHom).obj K) ≅
      (derivedPullback V.ι.toLRSHom.toShHom).obj K :=
  Scheme.derivedPullbackCompObj (X.homOfLE hVU) U.ι K ≪≫
    Scheme.derivedPullbackCongrObj (X.homOfLE_ι hVU) K

/-- `resComp` is natural in the object. -/
theorem resComp_hom_naturality {K L : DerivedCategory X.Modules} (χ : K ⟶ L) :
    (pullbackLE hVU).map ((derivedPullback U.ι.toLRSHom.toShHom).map χ) ≫
        (resComp hVU L).hom =
      (resComp hVU K).hom ≫ (derivedPullback V.ι.toLRSHom.toShHom).map χ := by
  have h₁ := (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
    (X.homOfLE hVU).toLRSHom.toShHom U.ι.toLRSHom.toShHom).hom.naturality χ
  have h₂ := derivedPullbackCongrObj_hom_naturality (X.homOfLE_ι hVU) χ
  dsimp only [resComp, Iso.trans_hom, Scheme.derivedPullbackCompObj, Iso.app_hom] at h₁ ⊢
  exact (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans
    ((Category.assoc _ _ _).trans ((_ ≫= h₂).trans (Category.assoc _ _ _).symm)))

/-- `resComp` as an isomorphism of functors. -/
def resCompIso :
    derivedPullback U.ι.toLRSHom.toShHom ⋙ pullbackLE hVU ≅
      derivedPullback V.ι.toLRSHom.toShHom :=
  NatIso.ofComponents (resComp hVU) (resComp_hom_naturality hVU)

/-- Restriction of sheaves of modules along the inclusion `V ⟶ U` of opens of `X` is additive. -/
local instance additiveSliceMap :
    (SheafOfModules.overMap.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)
      (homOfLE hVU)).Additive :=
  additiveOverMapSite (Stacks.SheafOfModules.ringedSite X.sheaf) (homOfLE hVU)

/-- Restriction of sheaves of modules along the inclusion `V ⟶ U` of opens of `X` preserves
finite limits. -/
local instance preservesFiniteLimitsSliceMap :
    PreservesFiniteLimits (SheafOfModules.overMap.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)
      (homOfLE hVU)) :=
  preservesFiniteLimitsOverMapSite (Stacks.SheafOfModules.ringedSite X.sheaf) (homOfLE hVU)

/-- Restriction of sheaves of modules along the inclusion `V ⟶ U` of opens of `X` preserves
finite colimits. -/
local instance preservesFiniteColimitsSliceMap :
    PreservesFiniteColimits (SheafOfModules.overMap.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)
      (homOfLE hVU)) :=
  preservesFiniteColimitsOverMapSite (Stacks.SheafOfModules.ringedSite X.sheaf) (homOfLE hVU)

/-- Restriction along `V ⟶ U` in the slice model. -/
abbrev sliceMap :=
  (SheafOfModules.overMap.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)
    (homOfLE hVU)).mapDerivedCategory

/-- The isomorphism of functors on the derived category of `X` comparing the two ways of reading
restriction from `U` to `V`. -/
def kappa :
    sliceRes U ⋙ (sliceMap hVU ⋙ toSubspace V) ≅ sliceRes U ⋙ (toSubspace U ⋙ pullbackLE hVU) :=
  Functor.isoWhiskerRight
      (AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso
        (Stacks.SheafOfModules.ringedSite X.sheaf) (homOfLE hVU)) (toSubspace V) ≪≫
    sliceIso V ≪≫ (resCompIso hVU).symm ≪≫
    Functor.isoWhiskerRight (sliceIso U).symm (pullbackLE hVU)

/-- The comparison `kappa`, descended to the derived category of the slice over `U`. -/
def theta : sliceMap hVU ⋙ toSubspace V ≅ toSubspace U ⋙ pullbackLE hVU :=
  haveI := sliceRes_isLocalization U
  Localization.liftNatIso (sliceRes U) (sliceW U) _ _ _ _
    (h₁ := Localization.Lifting.compLeft _ _ _) (h₂ := Localization.Lifting.compLeft _ _ _)
    (kappa hVU)

/-- `theta` at an object restricted from `X` is `kappa`. -/
theorem theta_hom_app (K : DerivedCategory X.Modules) :
    (theta hVU).hom.app ((sliceRes U).obj K) = (kappa hVU).hom.app K := by
  have := sliceRes_isLocalization U
  exact (@Localization.liftNatTrans_app _ _ _ _ (sliceRes U) (sliceW U) _ _ _ _ _
    (sliceMap hVU ⋙ toSubspace V) (toSubspace U ⋙ pullbackLE hVU)
    (Localization.Lifting.compLeft _ _ _) (Localization.Lifting.compLeft _ _ _)
    (kappa hVU).hom K).trans ((Category.id_comp _).trans (Category.comp_id _))

/-- **Conjugating a restriction by two compatible families of comparisons.** If `θ` identifies
the two composites `r ⋙ sV` and `sU ⋙ hp`, and at the two objects at hand is the composite of
the four comparisons, then conjugating `r.map ψ` and `sU.map ψ` by those comparisons gives the
same morphism. -/
theorem conj_restrict_eq {𝒮U 𝒮V 𝒯U 𝒯V : Type*} [Category* 𝒮U] [Category* 𝒮V] [Category* 𝒯U]
    [Category* 𝒯V] {r : 𝒮U ⥤ 𝒮V} {sV : 𝒮V ⥤ 𝒯V} {sU : 𝒮U ⥤ 𝒯U} {hp : 𝒯U ⥤ 𝒯V}
    (θ : r ⋙ sV ≅ sU ⋙ hp) {AK AL : 𝒮U} {BK BL : 𝒮V} {PUK PUL : 𝒯U} {PVK PVL : 𝒯V}
    (NK : r.obj AK ≅ BK) (NL : r.obj AL ≅ BL) (bK : sV.obj BK ≅ PVK) (bL : sV.obj BL ≅ PVL)
    (cK : hp.obj PUK ≅ PVK) (cL : hp.obj PUL ≅ PVL) (eK : sU.obj AK ≅ PUK) (eL : sU.obj AL ≅ PUL)
    (hK : θ.hom.app AK = sV.map NK.hom ≫ bK.hom ≫ cK.inv ≫ hp.map eK.inv)
    (hL : θ.hom.app AL = sV.map NL.hom ≫ bL.hom ≫ cL.inv ≫ hp.map eL.inv) (ψ : AK ⟶ AL) :
    bK.inv ≫ sV.map (NK.inv ≫ r.map ψ ≫ NL.hom) ≫ bL.hom =
      cK.inv ≫ hp.map (eK.inv ≫ sU.map ψ ≫ eL.hom) ≫ cL.hom := by
  have hθ' : sV.map (r.map ψ) = θ.hom.app AK ≫ hp.map (sU.map ψ) ≫ θ.inv.app AL := by
    simpa using θ.hom.naturality ψ =≫ θ.inv.app AL
  have hLi : θ.inv.app AL = hp.map eL.hom ≫ cL.hom ≫ bL.inv ≫ sV.map NL.inv := by
    rw [← cancel_epi (θ.hom.app AL), Iso.hom_inv_id_app, hL]
    simp [← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc, hθ', hK, hLi]
  simp [← Functor.map_comp_assoc, -Functor.map_comp]

omit hVU in
/-- A morphism between restrictions to the slice over `U`, read between the derived pullbacks
along `U ⟶ X`. -/
def homTransport (U : X.Opens) {K L : DerivedCategory X.Modules}
    (ψ : (sliceRes U).obj K ⟶ (sliceRes U).obj L) :
    (derivedPullback U.ι.toLRSHom.toShHom).obj K ⟶ (derivedPullback U.ι.toLRSHom.toShHom).obj L :=
  ((sliceIso U).app K).inv ≫ (toSubspace U).map ψ ≫ ((sliceIso U).app L).hom

omit hVU in
/-- The transport of the restriction of a morphism of `D(𝒪_X)` is its derived pullback. -/
theorem homTransport_map (U : X.Opens) {K L : DerivedCategory X.Modules} (χ : K ⟶ L) :
    homTransport U ((sliceRes U).map χ) = (derivedPullback U.ι.toLRSHom.toShHom).map χ :=
  (((sliceIso U).app K).inv ≫= (sliceIso U).hom.naturality χ).trans
    (Iso.inv_hom_id_app_assoc (sliceIso U) K _)

/-- **Restriction of morphisms in the two models.** Transporting the restriction along `V ⟶ U`
of a morphism of the slice model is restricting its transport along `V ⟶ U`, read through
`resComp`. -/
theorem homTransport_restrictDerivedHom {K L : DerivedCategory X.Modules}
    (ψ : (sliceRes U).obj K ⟶ (sliceRes U).obj L) :
    homTransport V (AlgebraicGeometry.RingedSite.restrictDerivedHom
        (Stacks.SheafOfModules.ringedSite X.sheaf) (homOfLE hVU) K L ψ) =
      (resComp hVU K).inv ≫ (pullbackLE hVU).map (homTransport U ψ) ≫ (resComp hVU L).hom :=
  conj_restrict_eq (theta hVU)
    ((AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) (homOfLE hVU)).app K)
    ((AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) (homOfLE hVU)).app L)
    ((sliceIso V).app K) ((sliceIso V).app L) (resComp hVU K) (resComp hVU L)
    ((sliceIso U).app K) ((sliceIso U).app L)
    (theta_hom_app hVU K) (theta_hom_app hVU L) ψ

omit hVU in
/-- Conjugation by two isomorphisms is injective. -/
theorem conj_cancel {𝒞 : Type*} [Category* 𝒞] {P Q P' Q' : 𝒞} (a : P ≅ Q) (b : P' ≅ Q')
    {x y : P ⟶ P'} (h : a.inv ≫ x ≫ b.hom = a.inv ≫ y ≫ b.hom) : x = y := by
  simpa using h

omit hVU in
/-- Conjugating back a conjugate. -/
theorem conj_conj {𝒞 : Type*} [Category* 𝒞] {P Q P' Q' : 𝒞} (a : P ≅ Q) (b : P' ≅ Q')
    (z : Q ⟶ Q') : a.inv ≫ (a.hom ≫ z ≫ b.inv) ≫ b.hom = z := by
  simp

omit hVU in
/-- The derived pullback along the inclusion of `⊤` is fully faithful. -/
def topFullyFaithful (X : Scheme.{u}) :
    (derivedPullback (⊤ : X.Opens).ι.toLRSHom.toShHom).FullyFaithful :=
  (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence
    ((Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace).mapIso
      X.topIso)).fullyFaithfulFunctor

omit hVU in
/-- **Glueing of morphisms of `D(𝒪_X)` along the derived pullbacks to a covering collection of
opens** (Stacks 0D66 (2)). Let `ℬ` be a collection of opens of a scheme `X` covering `X`, such
that the intersection of two members is the union of the members it contains, and let `K`, `L`
be objects of `D(𝒪_X)` with `Ext^n(K|_U, L|_U) = 0` for `n < 0` and `U ∈ ℬ`, restriction being
derived pullback along `U ⟶ X`. Then a family of morphisms `K|_U ⟶ L|_U`, `U ∈ ℬ`, compatible
with restriction along the inclusions `V ⟶ U` of members (read through `resComp`), comes from a
unique morphism `K ⟶ L`. -/
theorem existsUnique_hom_of_derivedPullback_opens (B : Set X.Opens) (hcover : sSup B = ⊤)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V = sSup {W | W ∈ B ∧ W ≤ U ⊓ V})
    {K L : DerivedCategory X.Modules}
    (hExt : ∀ U ∈ B, ∀ n : ℤ, n < 0 →
      Subsingleton (ShiftedHom ((derivedPullback U.ι.toLRSHom.toShHom).obj K)
        ((derivedPullback U.ι.toLRSHom.toShHom).obj L) n))
    (φ : ∀ U ∈ B, (derivedPullback U.ι.toLRSHom.toShHom).obj K ⟶
      (derivedPullback U.ι.toLRSHom.toShHom).obj L)
    (hφ : ∀ (U : X.Opens) (hU : U ∈ B) (V : X.Opens) (hV : V ∈ B) (hVU : V ≤ U),
      (resComp hVU K).inv ≫ (pullbackLE hVU).map (φ U hU) ≫ (resComp hVU L).hom = φ V hV) :
    ∃! ψ : K ⟶ L, ∀ (U : X.Opens) (hU : U ∈ B),
      (derivedPullback U.ι.toLRSHom.toShHom).map ψ = φ U hU := by
  have ff : ∀ U : X.Opens, (toSubspace U).FullyFaithful :=
    fun U ↦ (sliceSubspaceEquivalence U).fullyFaithfulFunctor
  have hinj : ∀ (U : X.Opens) {a b : (sliceRes U).obj K ⟶ (sliceRes U).obj L},
      homTransport U a = homTransport U b → a = b :=
    fun U _ _ h ↦ (ff U).map_injective (conj_cancel ((sliceIso U).app K) ((sliceIso U).app L) h)
  let φ' : ∀ W ∈ B, W ≤ ⊤ → ((sliceRes W).obj K ⟶ (sliceRes W).obj L) := fun W hW _ ↦
    (ff W).preimage (((sliceIso W).app K).hom ≫ φ W hW ≫ ((sliceIso W).app L).inv)
  have hφ' : ∀ W hW (h : W ≤ ⊤), homTransport W (φ' W hW h) = φ W hW := fun W hW _ ↦
    (congrArg (fun t ↦ ((sliceIso W).app K).inv ≫ t ≫ ((sliceIso W).app L).hom)
      ((ff W).map_preimage _)).trans (conj_conj ((sliceIso W).app K) ((sliceIso W).app L) _)
  have hExt' : ∀ U ∈ B, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((sliceRes U).obj K) ((sliceRes U).obj L) i) := fun U hU i hi ↦ by
    have := (ff U).faithful
    exact Stacks.DerivedGlueing.subsingleton_shiftedHom_of_faithful (toSubspace U) _ _ i
      (Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso ((sliceIso U).app K)
        ((sliceIso U).app L) i (hExt U hU i hi))
  let R : ∀ {W W' : X.Opens}, W' ≤ W →
      ((derivedPullback W.ι.toLRSHom.toShHom).obj K ⟶
        (derivedPullback W.ι.toLRSHom.toShHom).obj L) →
      ((derivedPullback W'.ι.toLRSHom.toShHom).obj K ⟶
        (derivedPullback W'.ι.toLRSHom.toShHom).obj L) :=
    fun h t ↦ (resComp h K).inv ≫ (pullbackLE h).map t ≫ (resComp h L).hom
  have hcompat : ∀ (W : X.Opens) (hW : W ∈ B) (hWO : W ≤ ⊤) (W' : X.Opens) (hW' : W' ∈ B)
      (h : W' ≤ W), AlgebraicGeometry.RingedSite.restrictDerivedHom
        (Stacks.SheafOfModules.ringedSite X.sheaf) h.hom K L (φ' W hW hWO) =
          φ' W' hW' (h.trans hWO) := fun W hW hWO W' hW' h ↦
    hinj W' ((homTransport_restrictDerivedHom h (φ' W hW hWO)).trans
      (((congrArg (R h) (hφ' W hW hWO)).trans (hφ W hW W' hW' h)).trans
        (hφ' W' hW' (h.trans hWO)).symm))
  have hO : (⊤ : X.Opens) = sSup {W | W ∈ B ∧ W ≤ ⊤} := by
    simpa using hcover.symm
  obtain ⟨ψt, hψt, huniq⟩ := Stacks.DerivedGlueing.existsUnique_hom_restrict_of_sSup_covered
    B hcover hinter K L hExt' ⊤ hO φ' hcompat
  let fT := topFullyFaithful X
  have hres : ∀ (U : X.Opens) (ψ : K ⟶ L),
      (derivedPullback U.ι.toLRSHom.toShHom).map ψ =
        R le_top ((derivedPullback (⊤ : X.Opens).ι.toLRSHom.toShHom).map ψ) := fun U ψ ↦ by
    dsimp only [R]
    rw [resComp_hom_naturality, Iso.inv_hom_id_assoc]
  refine ⟨fT.preimage (homTransport ⊤ ψt), fun U hU ↦ ?_, fun ψ'' hψ'' ↦ ?_⟩
  · exact (hres U _).trans <| (congrArg (R le_top) (fT.map_preimage _)).trans
      ((homTransport_restrictDerivedHom le_top ψt).symm.trans
      ((congrArg (homTransport U) (hψt U hU le_top)).trans (hφ' U hU le_top)))
  · have h₁ : (sliceRes ⊤).map ψ'' = ψt := by
      refine huniq _ fun W hW hWO ↦ hinj W ?_
      refine (congrArg (homTransport W)
        (AlgebraicGeometry.RingedSite.restrictDerivedHom_map
          (Stacks.SheafOfModules.ringedSite X.sheaf) hWO.hom K L ψ'')).trans ?_
      exact ((homTransport_map W ψ'').trans (hψ'' W hW)).trans (hφ' W hW hWO).symm
    exact fT.map_injective (((homTransport_map ⊤ ψ'').symm.trans
      (congrArg (homTransport ⊤) h₁)).trans (fT.map_preimage _).symm)

end AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing
