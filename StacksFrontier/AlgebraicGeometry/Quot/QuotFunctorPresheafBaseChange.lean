module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.SchemePoints
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorBaseChange

/-!
# The Quot presheaf commutes with base change (Stacks 08IT, 09TR)

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a quasi-coherent
`𝒪_X`-module, the standing data of Stacks 09TR, and let `p : B' ⟶ B` be a morphism of algebraic
spaces.  Set `X' = X ×_B B'` and let `F'` be the pullback of `F` to `X'`.  Stacks 08IT records
that for a scheme `T` over `B'` the quotients classified by `F'/X'/B'` at `T` are those
classified by `F/X/B` at `T`, read over `B` through `T ⟶ B' ⟶ B`.  This file proves the
corresponding statement for the Quot presheaf
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`: the Quot presheaf of `F'/X'/B'` is the
fibre product of the Quot presheaf of `F/X/B` and of `B'` over `B`.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.canonicalBaseChanged`: the standing data `F'/X'/B'` of
  the Quot functor; the morphism `X' ⟶ B'` is of finite presentation by Stacks 03XR.
* `AlgebraicGeometry.Space.QuotFamilyOver.ofCanonicalBaseChanged` and
  `AlgebraicGeometry.Space.QuotSituation.canonicalBaseChangedQuotSitePresheafHom`: a quotient of
  `F'/X'/B'` over `T ⟶ B'` read as a quotient of `F/X/B` over `T ⟶ B' ⟶ B`, and the resulting
  morphism of Quot presheaves.
* `AlgebraicGeometry.Space.QuotSituation.canonicalBaseChangedQuotSitePresheafIso`: the Quot
  presheaf of `F'/X'/B'` is the fibre product
  `Quot_{F/X/B} ×_B B'` in the category of presheaves on the schemes of the site.
* `AlgebraicGeometry.Space.QuotSituation.canonicalBaseChangedQuotSitePresheafObjEquiv` and
  `AlgebraicGeometry.Space.QuotSituation.canonicalBaseChangedQuotSitePullbackObjEquiv`: the
  objectwise description — a section over `T` is a morphism `b' : T ⟶ B'` together with a
  quotient of `F/X/B` over `T` lying over `b' ≫ p`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.mem_properlySupportedQuotients_canonicalBaseChanged_iff`
  and `AlgebraicGeometry.Space.QuotSituation.properlySupportedQuotientsCanonicalBaseChangeEquiv`:
  `Quot_{F'/X'/B'}(T) = Quot_{F/X/B}(T)`.
* `AlgebraicGeometry.Space.QuotSituation.isProperlySupportedOver_canonicalBaseChanged_iff`: proper
  support is transported along `X'_T ≅ X_T`.
* `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_baseChangeSubobjectEquiv`: the
  identification of the two lattices of subobjects is natural in the test scheme.
* `AlgebraicGeometry.Space.QuotSituation.isPullback_canonicalBaseChangedQuotSitePresheaf`: the
  square of Quot presheaves over `p : B' ⟶ B` is cartesian, and
  `AlgebraicGeometry.Space.QuotSituation.quotSitePresheafToBase_canonicalBaseChanged`: the
  canonical morphism to `B'` is the second projection of the fibre product.

## References

* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The `𝒪_{X_T}`-modules here have their sections in the universe `u` of the schemes, which the
-- ambient-universe abelian structure of the cohomology of modules on a site cannot describe.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Two coherences of the comparisons of inverse images -/

/-- The transport of a subobject along the equivalence induced by an isomorphism of algebraic
spaces, read through the comparison of a commuting square, is the conjugate of that subobject
by the inverse of the comparison. -/
theorem transportEquiv_modulePullbackSquare_eq_conjSubobject
    (hc : ModulePushforwardCoherence B S hS) {V W X Z : AlgebraicSpaces B S hS} (ε : V ≅ W)
    {l : W ⟶ Z} {r : V ⟶ X} {q : X ⟶ Z} {k : V ⟶ Z} (hk : ε.hom ≫ l = k)
    (hk' : r ≫ q = k) (F : Modules.{u, u} B S hS Z.1 Z.2)
    (K : Subobject ((modulePullback B S hS l).obj F)) :
    Subobject.transportEquiv (hc.modulePullbackEquivalence ε)
        ((modulePullbackSquare B S hS hk hk').app F) K =
      Functor.conjSubobject (modulePullbackSquare B S hS hk hk').symm K := by
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS ε.hom) :=
    (modulePullbackAdjunction B S hS ε.hom).leftAdjoint_preservesColimits
  have := Functor.preservesMonomorphisms_of_adjunction
    (hc.modulePullbackEquivalence ε).symm.toAdjunction
  have hm : Mono ((modulePullback B S hS ε.hom).map K.arrow ≫
      ((modulePullbackSquare B S hS hk hk').app F).hom) :=
    mono_comp' (Functor.map_mono (hc.modulePullbackEquivalence ε).functor K.arrow)
      (IsIso.mono_of_iso _)
  refine (Subobject.transportEquiv_eq_mk _ _ K).trans ?_
  symm
  refine Functor.conjSubobject_eq_mk_of_epi (modulePullbackSquare B S hS hk hk').symm (M := F) K
    ((modulePullback B S hS ε.hom).map K.arrow ≫ ((modulePullbackSquare B S hS hk hk').app F).hom)
    hm (𝟙 _) (IsIso.epi_of_iso _) ?_
  simp only [Iso.app_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact Category.comp_id _

/-- **Conjugating a quotient around a ladder of base changes.**  Let `q : X' ⟶ X` be a morphism
of algebraic spaces and consider spaces `A_T, A_U` over `X` and `A'_T, A'_U` over `X'`, joined by
morphisms `e_T : A'_T ⟶ A_T`, `e_U : A'_U ⟶ A_U` over `X` and `ρ : A_U ⟶ A_T`, `ρ' : A'_U ⟶ A'_T`
with `e_U ≫ ρ = ρ' ≫ e_T`.  For a module `F` on `X` and a quotient of the inverse image of `F` on
`A_T`, conjugating first along `e_T` and then along `ρ'` gives the same quotient of the inverse
image of `F` on `A'_U` as conjugating first along `ρ` and then along `e_U`. -/
theorem conjSubobject_modulePullbackTriangle_conjSubobject_modulePullbackSquare
    {X X' AT AU AT' AU' : AlgebraicSpaces B S hS} (q : X' ⟶ X) {sT : AT ⟶ X} {sU : AU ⟶ X}
    {sT' : AT' ⟶ X'} {sU' : AU' ⟶ X'} {eT : AT' ⟶ AT} {eU : AU' ⟶ AU} {ρ : AU ⟶ AT}
    {ρ' : AU' ⟶ AT'} {kT : AT' ⟶ X} {kU : AU' ⟶ X}
    (h1T : eT ≫ sT = kT) (h2T : sT' ≫ q = kT) (h1U : eU ≫ sU = kU) (h2U : sU' ≫ q = kU)
    (hρ : ρ ≫ sT = sU) (hρ' : ρ' ≫ sT' = sU') (hsq : eU ≫ ρ = ρ' ≫ eT)
    (F : Modules.{u, u} B S hS X.1 X.2) (K : Subobject ((modulePullback B S hS sT).obj F)) :
    Functor.conjSubobject (modulePullbackTriangle B S hS hρ')
        (M := (modulePullback B S hS q).obj F)
        (Functor.conjSubobject (modulePullbackSquare B S hS h1T h2T).symm K) =
      Functor.conjSubobject (modulePullbackSquare B S hS h1U h2U).symm
        (Functor.conjSubobject (modulePullbackTriangle B S hS hρ) K) := by
  have hc := modulePushforwardCoherence B S hS
  have hG : (ρ' ≫ eT) ≫ sT = kU := by
    rw [Category.assoc, h1T, ← h2T, ← Category.assoc, hρ', h2U]
  have hr : ρ' ≫ kT = kU := by rw [← h2T, ← Category.assoc, hρ', h2U]
  have eI := congrArg (fun i ↦ i.hom) (hc.modulePullbackTriangle_comp hρ' h2T hr h2U)
  have eII := congrArg (fun i ↦ i.hom)
    (hc.modulePullbackTriangle_comp (rfl : ρ' ≫ eT = ρ' ≫ eT) h1T hr hG)
  have eIII := congrArg (fun i ↦ i.hom) (hc.modulePullbackTriangle_comp hsq hρ h1U hG)
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom] at eI eII eIII
  have hfacL : (modulePullbackTriangle B S hS h2U).symm ≪≫ modulePullbackTriangle B S hS hG =
      ((Functor.isoWhiskerLeft (modulePullback B S hS q) (modulePullbackTriangle B S hS hρ') ≪≫
          (Functor.associator (modulePullback B S hS q) (modulePullback B S hS sT')
            (modulePullback B S hS ρ')).symm) ≪≫
          Functor.isoWhiskerRight (modulePullbackSquare B S hS h1T h2T).symm
            (modulePullback B S hS ρ') ≪≫
          Functor.associator (modulePullback B S hS sT) (modulePullback B S hS eT)
            (modulePullback B S hS ρ')) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS sT)
          (modulePullbackTriangle B S hS (rfl : ρ' ≫ eT = ρ' ≫ eT))).symm := by
    refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
    have hI := congrArg (fun t ↦ t.app M) eI
    have hII := congrArg (fun t ↦ t.app M) eII
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id] at hI hII
    simp only [modulePullbackSquare, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
      CategoryTheory.Functor.map_comp]
    refine (Iso.inv_comp_eq ((modulePullbackTriangle B S hS h2U).app M)).2 ?_
    rw [Iso.app_hom, ← Category.assoc, hI, Category.assoc,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc, ← hII, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hfacR : (modulePullbackTriangle B S hS h2U).symm ≪≫ modulePullbackTriangle B S hS hG =
      ((modulePullbackSquare B S hS h1U h2U).symm ≪≫
          Functor.isoWhiskerRight (modulePullbackTriangle B S hS hρ)
            (modulePullback B S hS eU) ≪≫
          Functor.associator (modulePullback B S hS sT) (modulePullback B S hS ρ)
            (modulePullback B S hS eU)) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS sT)
          (modulePullbackTriangle B S hS hsq)).symm := by
    refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
    have hIII := congrArg (fun t ↦ t.app M) eIII
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id] at hIII
    simp only [modulePullbackSquare, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.id_comp, Category.assoc]
    refine (Iso.inv_comp_eq ((modulePullbackTriangle B S hS h2U).app M)).2 ?_
    rw [Iso.app_hom, Iso.hom_inv_id_app_assoc, ← Category.assoc, ← hIII, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hLeft := Functor.conjSubobject_comp (modulePullbackSquare B S hS h1T h2T).symm
    (Functor.isoWhiskerLeft (modulePullback B S hS q) (modulePullbackTriangle B S hS hρ') ≪≫
      (Functor.associator (modulePullback B S hS q) (modulePullback B S hS sT')
        (modulePullback B S hS ρ')).symm)
    _ (modulePullbackTriangle B S hS (rfl : ρ' ≫ eT = ρ' ≫ eT)) hfacL K
  have hRight := Functor.conjSubobject_comp (modulePullbackTriangle B S hS hρ)
    (modulePullbackSquare B S hS h1U h2U).symm _ (modulePullbackTriangle B S hS hsq) hfacR K
  have hw : Functor.conjSubobject (P₁ := modulePullback B S hS q ⋙ modulePullback B S hS sT')
      (L := modulePullback B S hS ρ')
      (Functor.isoWhiskerLeft (modulePullback B S hS q) (modulePullbackTriangle B S hS hρ') ≪≫
        (Functor.associator (modulePullback B S hS q) (modulePullback B S hS sT')
          (modulePullback B S hS ρ')).symm) (M := F)
        (Functor.conjSubobject (modulePullbackSquare B S hS h1T h2T).symm K) =
      Functor.conjSubobject (modulePullbackTriangle B S hS hρ')
        (M := (modulePullback B S hS q).obj F)
        (Functor.conjSubobject (modulePullbackSquare B S hS h1T h2T).symm K) := by
    simp only [Functor.conjSubobject, Functor.conjQuotientProjection, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Category.comp_id]
  rw [← hw, ← hLeft, hRight]

/-! ### Naturality of the identification of the two lattices of subobjects -/

namespace QuotientSituation

variable (D : QuotientSituation B S hS) {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y)
  (hF : (D.baseChangedSourceModule p).IsQuasicoherentOnSite)

/-- The identification `X'_T ≅ X_T` is compatible with the morphisms of base changes induced by a
morphism `U ⟶ T` of test schemes over `B'`. -/
theorem baseChangeFiberIso_hom_comp_relativeMap {U T : SchemesOver Y'} (h : U ⟶ T) :
    (D.baseChangeFiberIso p hF U).hom ≫ D.relativeMap ((CostructuredArrow.map p).map h) =
      (D.baseChangedSituation p hF).relativeMap h ≫ (D.baseChangeFiberIso p hF T).hom := by
  refine baseChange_hom_ext D.f ?_ ?_
  · have h1 := D.baseChangeFiberIso_hom_comp_sourceProjection p hF U
    have h2 := D.baseChangeFiberIso_hom_comp_sourceProjection p hF T
    have h3 := baseChangeMap_comp_projection D.f ((CostructuredArrow.map p).map h)
    have h4 := baseChangeMap_comp_projection (D.baseChangedSituation p hF).f h
    simp only [Category.assoc] at h1 h2 h3 h4 ⊢
    rw [h3, h1, h2]
    exact ((reassoc_of% h4) (D.baseChangedSourceProjection p)).symm
  · have h1 := D.baseChangeFiberIso_hom_comp_projection p hF U
    have h2 := D.baseChangeFiberIso_hom_comp_projection p hF T
    have h3 := baseChangeMap_comp_inclusion D.f ((CostructuredArrow.map p).map h)
    have h4 := baseChangeMap_comp_inclusion (D.baseChangedSituation p hF).f h
    simp only [Category.assoc] at h1 h2 h3 h4 ⊢
    rw [h3, ← Category.assoc, h1, h2, h4]
    rfl

/-- The identification of the subobjects of `F_T` with those of `F'_T` is the conjugation of
quotients by the inverse of the comparison of Stacks 03LU for the square
`X'_T ⟶ X_T ⟶ X`, `X'_T ⟶ X' ⟶ X`. -/
theorem baseChangeSubobjectEquiv_eq_conjSubobject (hc : ModulePushforwardCoherence B S hS)
    (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.baseChangeSubobjectEquiv p hF hc T K =
      Functor.conjSubobject (modulePullbackSquare B S hS
        (D.baseChangeFiberIso_hom_comp_sourceProjection p hF T) rfl).symm K :=
  transportEquiv_modulePullbackSquare_eq_conjSubobject hc (D.baseChangeFiberIso p hF T) _ _ D.F K

/-- **The identification of Stacks 08IT is natural in the test scheme.**  For a morphism
`h : U ⟶ T` of test schemes over `B'`, pulling back a quotient of `F'_T` along `X'_U ⟶ X'_T`
corresponds to pulling back the matching quotient of `F_T` along `X_U ⟶ X_T`. -/
theorem quotientPullback_baseChangeSubobjectEquiv (hc : ModulePushforwardCoherence B S hS)
    {U T : SchemesOver Y'} (h : U ⟶ T)
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    (D.baseChangedSituation p hF).quotientPullback h (D.baseChangeSubobjectEquiv p hF hc T K) =
      D.baseChangeSubobjectEquiv p hF hc U
        (D.quotientPullback ((CostructuredArrow.map p).map h) K) := by
  rw [D.baseChangeSubobjectEquiv_eq_conjSubobject p hF hc T K,
    D.baseChangeSubobjectEquiv_eq_conjSubobject p hF hc U]
  exact conjSubobject_modulePullbackTriangle_conjSubobject_modulePullbackSquare
    (D.baseChangedSourceProjection p)
    (D.baseChangeFiberIso_hom_comp_sourceProjection p hF T) rfl
    (D.baseChangeFiberIso_hom_comp_sourceProjection p hF U) rfl
    (baseChangeMap_comp_projection D.f ((CostructuredArrow.map p).map h))
    (baseChangeMap_comp_projection (D.baseChangedSituation p hF).f h)
    (D.baseChangeFiberIso_hom_comp_relativeMap p hF h) D.F K

/-- The canonical identification of the subobjects of `F_T` with those of `F'_T`, at the
canonical values of its two inputs. -/
abbrev canonicalBaseChangeSubobjectEquiv (T : SchemesOver Y') :
    Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T)) ≃
      Subobject ((D.canonicalBaseChangedSituation p).baseChangeModule T) :=
  D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
    (modulePushforwardCoherence B S hS) T

/-- **Naturality of the canonical identification of Stacks 08IT** in the test scheme. -/
theorem quotientPullback_canonicalBaseChangeSubobjectEquiv {U T : SchemesOver Y'} (h : U ⟶ T)
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    (D.canonicalBaseChangedSituation p).quotientPullback h
        (D.canonicalBaseChangeSubobjectEquiv p T K) =
      D.canonicalBaseChangeSubobjectEquiv p U
        (D.quotientPullback ((CostructuredArrow.map p).map h) K) :=
  D.quotientPullback_baseChangeSubobjectEquiv p _ (modulePushforwardCoherence B S hS) h K

/-- The inverse form of the naturality of the canonical identification. -/
theorem canonicalBaseChangeSubobjectEquiv_symm_quotientPullback {U T : SchemesOver Y'}
    (h : U ⟶ T) (L : Subobject ((D.canonicalBaseChangedSituation p).baseChangeModule T)) :
    (D.canonicalBaseChangeSubobjectEquiv p U).symm
        ((D.canonicalBaseChangedSituation p).quotientPullback h L) =
      D.quotientPullback ((CostructuredArrow.map p).map h)
        ((D.canonicalBaseChangeSubobjectEquiv p T).symm L) := by
  rw [Equiv.symm_apply_eq, ← D.quotientPullback_canonicalBaseChangeSubobjectEquiv p h,
    Equiv.apply_symm_apply]

end QuotientSituation

/-! ### Proper support along an isomorphism of algebraic spaces -/

/-- **Proper support is carried along an isomorphism of algebraic spaces over a common base.**
For an isomorphism `e : A' ≅ A` over `Z`, if a finite type quasi-coherent module `G` on `A` has
support proper over `Z`, then so does its inverse image on `A'`. -/
theorem hasProperSupport_modulePullback_of_iso {A A' Z : AlgebraicSpaces B S hS} (e : A' ≅ A)
    {π : A ⟶ Z} {π' : A' ⟶ Z} (hπ : e.hom ≫ π = π') (hlft : IsLocallyOfFiniteType B S hS π.hom)
    (hlft' : IsLocallyOfFiniteType B S hS π'.hom) (G : Modules.{u, u} B S hS A.1 A.2)
    (hqc : SheafOfModules.IsQuasicoherentOnSite G) (hft : SheafOfModules.IsFiniteTypeOnSite G)
    (h : HasProperSupport B S hS A.2 Z.2 π.hom hlft ((SheafOfModules.toSheaf _).obj G)) :
    HasProperSupport B S hS A'.2 Z.2 π'.hom hlft'
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS e.hom).obj G)) := by
  obtain ⟨_, hproper⟩ := h
  have sq : IsPullback e.hom π' π (𝟙 Z) :=
    IsPullback.of_horiz_isIso ⟨by rw [hπ, Category.comp_id]⟩
  exact ⟨isClosed_supportOfSheaf_modulePullback B S hS e.hom G hft,
    isProperOver_supportOfSheaf_modulePullback B S hS sq hlft G hqc hft hproper⟩

namespace QuotSituation

variable (D : QuotSituation B S hS) {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y)

/-! ### The base-changed situation of the Quot functor -/

/-- **Stacks 08IT, for the standing data of Stacks 09TR.**  Changing the base algebraic space
along `p : B' ⟶ B` gives again the standing data of the Quot functor: the situation
`F'/X'/B'` of `AlgebraicGeometry.Space.QuotientSituation.canonicalBaseChangedSituation`, whose
morphism `X' = X ×_B B' ⟶ B'` is of finite presentation as a base change of `X ⟶ B`
(Stacks 03XR). -/
abbrev canonicalBaseChanged : QuotSituation B S hS where
  X := D.baseChangedSource p
  Y := Y'
  f := D.baseChangedMorphism p
  F := D.baseChangedSourceModule p
  quasicoherent := D.isQuasicoherentOnSite_baseChangedSourceModule p
  finitePresentation := (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f p) D.finitePresentation

/-- The underlying quotient situation of `canonicalBaseChanged` is
`AlgebraicGeometry.Space.QuotientSituation.canonicalBaseChangedSituation`. -/
theorem canonicalBaseChanged_toQuotientSituation :
    (D.canonicalBaseChanged p).toQuotientSituation =
      D.toQuotientSituation.canonicalBaseChangedSituation p :=
  rfl

/-- The identification `X'_T ≅ X_T` of the base change of `X'` along a test scheme `T` over
`B'` with the base change of `X` along the same scheme read over `B`. -/
abbrev canonicalBaseChangeFiberIso (T : SchemesOver Y') :
    (D.canonicalBaseChanged p).space T ≅ D.space ((CostructuredArrow.map p).obj T) :=
  D.toQuotientSituation.baseChangeFiberIso p
    (D.toQuotientSituation.isQuasicoherentOnSite_baseChangedSourceModule p) T

/-- The identification of the subobjects of `F_T` with those of `F'_T`. -/
abbrev canonicalBaseChangeSubobjectEquiv (T : SchemesOver Y') :
    Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T)) ≃
      Subobject ((D.canonicalBaseChanged p).baseChangeModule T) :=
  D.toQuotientSituation.canonicalBaseChangeSubobjectEquiv p T

/-- **The quotients correspond**: the quotient of `F'_T` by the subobject matching `K` is the
inverse image along `X'_T ≅ X_T` of the quotient `F_T/K`. -/
def canonicalBaseChangedQuotientModuleIso (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    (D.canonicalBaseChanged p).quotientModule T (D.canonicalBaseChangeSubobjectEquiv p T K) ≅
      (modulePullback B S hS (D.canonicalBaseChangeFiberIso p T).hom).obj
        (D.quotientModule ((CostructuredArrow.map p).obj T) K) :=
  D.toQuotientSituation.canonicalBaseChangeQuotientModuleIso p T K

/-- **The quotients correspond**, read from a subobject `L` of `F'_T`: the quotient `F'_T/L` is
the inverse image along `X'_T ≅ X_T` of the quotient of `F_T` by the matching subobject. -/
def canonicalBaseChangedQuotientModuleIsoSymm (T : SchemesOver Y')
    (L : Subobject ((D.canonicalBaseChanged p).baseChangeModule T)) :
    (D.canonicalBaseChanged p).quotientModule T L ≅
      (modulePullback B S hS (D.canonicalBaseChangeFiberIso p T).hom).obj
        (D.quotientModule ((CostructuredArrow.map p).obj T)
          ((D.canonicalBaseChangeSubobjectEquiv p T).symm L)) :=
  eqToIso (congrArg ((D.canonicalBaseChanged p).quotientModule T)
      ((D.canonicalBaseChangeSubobjectEquiv p T).apply_symm_apply L).symm) ≪≫
    D.canonicalBaseChangedQuotientModuleIso p T _

/-- **Proper support moves across the identification `X'_T ≅ X_T`.**  For a quotient in
`Q^{fp}_{F/X/B}(T)`, the quotient of `F'_T` by the matching subobject has support proper over
`T` exactly when `F_T/K` does. -/
theorem isProperlySupportedOver_canonicalBaseChanged_iff (T : SchemesOver Y')
    {K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))}
    (hK : K ∈ D.finitePresentationQuotients ((CostructuredArrow.map p).obj T)) :
    (D.canonicalBaseChanged p).IsProperlySupportedOver T
        ((D.canonicalBaseChanged p).quotientModule T (D.canonicalBaseChangeSubobjectEquiv p T K)) ↔
      D.IsProperlySupportedOver ((CostructuredArrow.map p).obj T)
        (D.quotientModule ((CostructuredArrow.map p).obj T) K) := by
  let e := D.canonicalBaseChangeFiberIso p T
  have hπ : e.hom ≫ D.projection ((CostructuredArrow.map p).obj T) =
      (D.canonicalBaseChanged p).projection T :=
    D.toQuotientSituation.baseChangeFiberIso_hom_comp_projection p _ T
  have hπ' : e.symm.hom ≫ (D.canonicalBaseChanged p).projection T =
      D.projection ((CostructuredArrow.map p).obj T) := by
    rw [← hπ, Iso.symm_hom, Iso.inv_hom_id_assoc]
  have hqc : (D.quotientModule ((CostructuredArrow.map p).obj T) K).IsQuasicoherentOnSite :=
    hK.1.1
  let := hK.2
  have hft : (D.quotientModule ((CostructuredArrow.map p).obj T) K).IsFiniteTypeOnSite :=
    inferInstance
  have hqc' : ((modulePullback B S hS e.hom).obj
      (D.quotientModule ((CostructuredArrow.map p).obj T) K)).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_modulePullback_iso_iff (modulePushforwardCoherence B S hS) e _).2 hqc
  let := isFinitePresentationOnSite_modulePullback B S hS e.hom _ hK.2
  have hft' : ((modulePullback B S hS e.hom).obj
      (D.quotientModule ((CostructuredArrow.map p).obj T) K)).IsFiniteTypeOnSite :=
    inferInstance
  constructor
  · intro h
    have h₁ := (D.canonicalBaseChanged p).isProperlySupportedOver_of_iso
      (D.canonicalBaseChangedQuotientModuleIso p T K) h
    have h₂ := hasProperSupport_modulePullback_of_iso e.symm hπ'
      ((D.canonicalBaseChanged p).isLocallyOfFiniteType_projection T)
      (D.isLocallyOfFiniteType_projection _) _ hqc' hft' h₁
    exact D.isProperlySupportedOver_of_iso
      (((modulePushforwardCoherence B S hS).modulePullbackEquivalence e).unitIso.app _).symm h₂
  · intro h
    exact (D.canonicalBaseChanged p).isProperlySupportedOver_of_iso
      (D.canonicalBaseChangedQuotientModuleIso p T K).symm
      (hasProperSupport_modulePullback_of_iso e hπ (D.isLocallyOfFiniteType_projection _)
        ((D.canonicalBaseChanged p).isLocallyOfFiniteType_projection T) _ hqc hft h)

/-- **Stacks 08IT for the Quot functor, in membership form.**  For a test scheme `T` over `B'`
a subobject of `F'_T` is an element of `Quot_{F'/X'/B'}(T)` exactly when the matching subobject
of `F_T` is an element of `Quot_{F/X/B}(T)`, with `T` read over `B` through `T ⟶ B' ⟶ B`. -/
theorem mem_properlySupportedQuotients_canonicalBaseChanged_iff (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.canonicalBaseChangeSubobjectEquiv p T K ∈
        (D.canonicalBaseChanged p).properlySupportedQuotients T ↔
      K ∈ D.properlySupportedQuotients ((CostructuredArrow.map p).obj T) := by
  have hfp := D.toQuotientSituation.mem_finitePresentationQuotients_canonicalBaseChange_iff p T K
  exact ⟨fun ⟨h₁, h₂⟩ ↦
      ⟨hfp.1 h₁, (D.isProperlySupportedOver_canonicalBaseChanged_iff p T (hfp.1 h₁)).1 h₂⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨hfp.2 h₁, (D.isProperlySupportedOver_canonicalBaseChanged_iff p T h₁).2 h₂⟩⟩

/-- **Stacks 08IT for the Quot functor.**  `Quot_{F'/X'/B'}(T) = Quot_{F/X/B}(T)` under the
canonical identification of the two lattices of subobjects. -/
theorem properlySupportedQuotients_canonicalBaseChanged (T : SchemesOver Y') :
    (D.canonicalBaseChanged p).properlySupportedQuotients T =
      D.canonicalBaseChangeSubobjectEquiv p T ''
        D.properlySupportedQuotients ((CostructuredArrow.map p).obj T) := by
  refine Set.Subset.antisymm (fun L hL ↦ ?_) (fun L hL ↦ ?_)
  · refine ⟨(D.canonicalBaseChangeSubobjectEquiv p T).symm L, ?_,
      (D.canonicalBaseChangeSubobjectEquiv p T).apply_symm_apply L⟩
    refine (D.mem_properlySupportedQuotients_canonicalBaseChanged_iff p T _).1 ?_
    rwa [Equiv.apply_symm_apply]
  · obtain ⟨K, hK, rfl⟩ := hL
    exact (D.mem_properlySupportedQuotients_canonicalBaseChanged_iff p T K).2 hK

/-- **Stacks 08IT for the Quot functor**, as a bijection
`Quot_{F/X/B}(T) ≃ Quot_{F'/X'/B'}(T)`. -/
def properlySupportedQuotientsCanonicalBaseChangeEquiv (T : SchemesOver Y') :
    D.properlySupportedQuotients ((CostructuredArrow.map p).obj T) ≃
      (D.canonicalBaseChanged p).properlySupportedQuotients T :=
  (D.canonicalBaseChangeSubobjectEquiv p T).subtypeEquiv fun K ↦
    (D.mem_properlySupportedQuotients_canonicalBaseChanged_iff p T K).symm

/-- **Naturality of the identification in the test scheme**, for the base-changed Quot
situation. -/
theorem quotientPullback_canonicalBaseChangeSubobjectEquiv {U T : SchemesOver Y'} (h : U ⟶ T)
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    (D.canonicalBaseChanged p).quotientPullback h (D.canonicalBaseChangeSubobjectEquiv p T K) =
      D.canonicalBaseChangeSubobjectEquiv p U
        (D.quotientPullback ((CostructuredArrow.map p).map h) K) :=
  D.toQuotientSituation.quotientPullback_canonicalBaseChangeSubobjectEquiv p h K

/-- The inverse form of the naturality of the identification, for the base-changed Quot
situation. -/
theorem canonicalBaseChangeSubobjectEquiv_symm_quotientPullback {U T : SchemesOver Y'}
    (h : U ⟶ T) (L : Subobject ((D.canonicalBaseChanged p).baseChangeModule T)) :
    (D.canonicalBaseChangeSubobjectEquiv p U).symm
        ((D.canonicalBaseChanged p).quotientPullback h L) =
      D.quotientPullback ((CostructuredArrow.map p).map h)
        ((D.canonicalBaseChangeSubobjectEquiv p T).symm L) :=
  D.toQuotientSituation.canonicalBaseChangeSubobjectEquiv_symm_quotientPullback p h L

end QuotSituation

/-! ### The Quot presheaf of the base-changed situation -/

namespace QuotSituation

variable (D : QuotSituation B S hS) {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y)

/-- Pulling back a quotient along two morphisms of test schemes with the same underlying morphism
of schemes gives the same quotient; the two morphisms to `B` they lie over need only be equal,
so the two kernels are compared heterogeneously. -/
theorem quotientPullback_heq {T T' : BigFppfOver B S hS}
    {t : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y} {t₁ t₂ : (schemeSpaceFunctor B S hS).obj T' ⟶ D.Y}
    (ht : t₁ = t₂) (m₁ : CostructuredArrow.mk t₁ ⟶ CostructuredArrow.mk t)
    (m₂ : CostructuredArrow.mk t₂ ⟶ CostructuredArrow.mk t) (hm : m₁.left = m₂.left)
    (K : Subobject (D.baseChangeModule (CostructuredArrow.mk t))) :
    D.quotientPullback m₁ K ≍ D.quotientPullback m₂ K := by
  subst ht
  obtain rfl : m₁ = m₂ := CostructuredArrow.hom_ext _ _ hm
  rfl

end QuotSituation

namespace QuotFamilyOver

variable {D : QuotSituation B S hS} {Y' : AlgebraicSpaces B S hS} {p : Y' ⟶ D.Y}

/-- A quotient of the base-changed situation `F'/X'/B'` over a scheme `T` of the site, read as a
quotient of `F/X/B` over `T`: it lies over the composite `T ⟶ B' ⟶ B`, and its kernel is the
subobject of `F_T` matching the kernel in `F'_T` (Stacks 08IT). -/
def ofCanonicalBaseChanged {T : BigFppfOver B S hS}
    (y : QuotFamilyOver (D.canonicalBaseChanged p) T) : QuotFamilyOver D T where
  toBase := y.toBase ≫ p
  subobject := (D.canonicalBaseChangeSubobjectEquiv p (CostructuredArrow.mk y.toBase)).symm
    y.subobject
  mem := (D.mem_properlySupportedQuotients_canonicalBaseChanged_iff p
      (CostructuredArrow.mk y.toBase) _).1
    ((congrArg (fun L ↦ L ∈ (D.canonicalBaseChanged p).properlySupportedQuotients
        (CostructuredArrow.mk y.toBase))
      ((D.canonicalBaseChangeSubobjectEquiv p (CostructuredArrow.mk y.toBase)).apply_symm_apply
        y.subobject)).mpr y.mem)

/-- A quotient of `F'/X'/B'` read over `B` lies over the composite `T ⟶ B' ⟶ B`. -/
@[simp]
theorem ofCanonicalBaseChanged_toBase {T : BigFppfOver B S hS}
    (y : QuotFamilyOver (D.canonicalBaseChanged p) T) :
    y.ofCanonicalBaseChanged.toBase = y.toBase ≫ p :=
  rfl

/-- The kernel of a quotient of `F'/X'/B'` read over `B` is the matching subobject of `F_T`. -/
theorem ofCanonicalBaseChanged_subobject {T : BigFppfOver B S hS}
    (y : QuotFamilyOver (D.canonicalBaseChanged p) T) :
    y.ofCanonicalBaseChanged.subobject =
      (D.canonicalBaseChangeSubobjectEquiv p (CostructuredArrow.mk y.toBase)).symm y.subobject :=
  rfl

/-- Reading a quotient of `F'/X'/B'` over `B` commutes with base change along a morphism
`T' ⟶ T` of the site. -/
theorem ofCanonicalBaseChanged_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (y : QuotFamilyOver (D.canonicalBaseChanged p) T) :
    (y.baseChange g).ofCanonicalBaseChanged = y.ofCanonicalBaseChanged.baseChange g := by
  refine QuotFamilyOver.ext (Category.assoc _ _ _) ?_
  have e := D.canonicalBaseChangeSubobjectEquiv_symm_quotientPullback p
    (restrict g y.toBase) y.subobject
  exact (heq_of_eq e).trans <| D.quotientPullback_heq (t := y.toBase ≫ p)
    (t₁ := ((schemeSpaceFunctor B S hS).map g ≫ y.toBase) ≫ p)
    (t₂ := (schemeSpaceFunctor B S hS).map g ≫ y.toBase ≫ p) (Category.assoc _ _ _)
    ((CostructuredArrow.map p).map (restrict g y.toBase)) (restrict g (y.toBase ≫ p)) rfl
    ((D.canonicalBaseChangeSubobjectEquiv p (CostructuredArrow.mk y.toBase)).symm y.subobject)

end QuotFamilyOver

namespace QuotSituation

variable (D : QuotSituation B S hS) {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y)

/-- **Stacks 08IT for the Quot presheaf, the comparison morphism.**  The morphism from the Quot
presheaf of the base-changed situation `F'/X'/B'` to the Quot presheaf of `F/X/B`, reading a
quotient over `T ⟶ B'` as a quotient over `T ⟶ B' ⟶ B`. -/
def canonicalBaseChangedQuotSitePresheafHom :
    (D.canonicalBaseChanged p).quotSitePresheaf ⟶ D.quotSitePresheaf where
  app T := TypeCat.ofHom fun y ↦ y.ofCanonicalBaseChanged
  naturality T T' g := by
    ext y
    exact QuotFamilyOver.ofCanonicalBaseChanged_baseChange g.unop y

/-- The comparison morphism sends a quotient of `F'/X'/B'` to the same quotient read over `B`. -/
@[simp]
theorem canonicalBaseChangedQuotSitePresheafHom_app_apply (T : (BigFppfOver B S hS)ᵒᵖ)
    (y : (D.canonicalBaseChanged p).quotSitePresheaf.obj T) :
    (D.canonicalBaseChangedQuotSitePresheafHom p).app T y = y.ofCanonicalBaseChanged :=
  rfl

/-- The comparison morphism lies over `p : B' ⟶ B`. -/
theorem canonicalBaseChangedQuotSitePresheafHom_comp_quotSitePresheafToBase :
    D.canonicalBaseChangedQuotSitePresheafHom p ≫ D.quotSitePresheafToBase =
      (D.canonicalBaseChanged p).quotSitePresheafToBase ≫
        Functor.whiskerRight p.hom uliftFunctor.{u + 1, u} := by
  ext T y
  exact congrArg ULift.up (yonedaEquiv_comp y.toBase.hom p.hom)

/-- The injectivity half of the objectwise description: a quotient of `F'/X'/B'` over a scheme
`T` of the site is determined by the morphism `T ⟶ B'` it lies over and by the quotient of
`F/X/B` it is read as. -/
theorem canonicalBaseChangedQuotSitePresheafHom_injective {T : BigFppfOver B S hS}
    {y₁ y₂ : QuotFamilyOver (D.canonicalBaseChanged p) T}
    (h₁ : y₁.ofCanonicalBaseChanged = y₂.ofCanonicalBaseChanged) (h₂ : y₁.toBase = y₂.toBase) :
    y₁ = y₂ := by
  obtain ⟨b₁, s₁, m₁⟩ := y₁
  obtain ⟨b₂, s₂, m₂⟩ := y₂
  change b₁ = b₂ at h₂
  subst h₂
  have h := (QuotFamilyOver.mk.inj h₁).2
  obtain rfl : s₁ = s₂ := (D.canonicalBaseChangeSubobjectEquiv p _).symm.injective (eq_of_heq h)
  rfl

/-- The surjectivity half of the objectwise description: a quotient `x` of `F/X/B` over `T`
lying over `b' ≫ p` comes from a quotient of `F'/X'/B'` over `T` lying over `b'`. -/
theorem exists_ofCanonicalBaseChanged_eq {T : BigFppfOver B S hS}
    (b' : (schemeSpaceFunctor B S hS).obj T ⟶ Y') (x : QuotFamilyOver D T)
    (hx : x.toBase = b' ≫ p) :
    ∃ y : QuotFamilyOver (D.canonicalBaseChanged p) T,
      y.ofCanonicalBaseChanged = x ∧ y.toBase = b' := by
  obtain ⟨t, K, hK⟩ := x
  change t = b' ≫ p at hx
  subst hx
  refine ⟨⟨b', D.canonicalBaseChangeSubobjectEquiv p (CostructuredArrow.mk b') K,
    (D.mem_properlySupportedQuotients_canonicalBaseChanged_iff p (CostructuredArrow.mk b') K).2
      hK⟩, ?_, rfl⟩
  exact QuotFamilyOver.ext rfl (heq_of_eq (Equiv.symm_apply_apply _ K))

/-- **Stacks 08IT for the Quot presheaf.**  The Quot presheaf of the base-changed situation
`F'/X'/B'` is the fibre product of the Quot presheaf of `F/X/B` and of `B'` over `B`: the square
formed by the comparison morphism, the two canonical morphisms to the bases and `p : B' ⟶ B` is
cartesian in the category of presheaves on the schemes of the site. -/
theorem isPullback_canonicalBaseChangedQuotSitePresheaf :
    IsPullback (D.canonicalBaseChangedQuotSitePresheafHom p)
      (D.canonicalBaseChanged p).quotSitePresheafToBase D.quotSitePresheafToBase
      (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u}) := by
  refine IsPullback.of_forall_isPullback_app fun T ↦ ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun t ↦ t.app T)
      (D.canonicalBaseChangedQuotSitePresheafHom_comp_quotSitePresheafToBase p), ?_, ?_⟩
  · rintro y₁ y₂ ⟨h₁, h₂⟩
    exact D.canonicalBaseChangedQuotSitePresheafHom_injective p h₁
      (schemeSpaceSection_injective (congrArg ULift.down h₂))
  · intro x z hxz
    obtain ⟨zd⟩ := z
    let b' : (schemeSpaceFunctor B S hS).obj T.unop ⟶ Y' :=
      ObjectProperty.homMk (yonedaEquiv.symm zd)
    have hx : x.toBase = b' ≫ p := by
      refine schemeSpaceSection_injective ((congrArg ULift.down hxz).trans ?_)
      refine Eq.trans ?_ (yonedaEquiv_comp b'.hom p.hom).symm
      exact congrArg (p.hom.app T) (yonedaEquiv.apply_symm_apply zd).symm
    obtain ⟨y, hy, hyb⟩ := D.exists_ofCanonicalBaseChanged_eq p b' x hx
    exact ⟨y, hy, congrArg ULift.up ((congrArg (fun a ↦ yonedaEquiv a.hom) hyb).trans
      (yonedaEquiv.apply_symm_apply zd))⟩

/-- **Stacks 08IT for the Quot presheaf.**  The Quot presheaf of the base-changed situation
`F'/X'/B'` is isomorphic to the fibre product of the canonical morphism from the Quot presheaf
of `F/X/B` to `B` and of `p : B' ⟶ B`. -/
def canonicalBaseChangedQuotSitePresheafIso :
    (D.canonicalBaseChanged p).quotSitePresheaf ≅
      Limits.pullback D.quotSitePresheafToBase
        (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u}) :=
  (D.isPullback_canonicalBaseChangedQuotSitePresheaf p).isoPullback

/-- The identification with the fibre product followed by its first projection is the comparison
morphism. -/
@[reassoc (attr := simp)]
theorem canonicalBaseChangedQuotSitePresheafIso_hom_fst :
    (D.canonicalBaseChangedQuotSitePresheafIso p).hom ≫ Limits.pullback.fst _ _ =
      D.canonicalBaseChangedQuotSitePresheafHom p :=
  IsPullback.isoPullback_hom_fst _

/-- The identification with the fibre product followed by its second projection is the canonical
morphism from the Quot presheaf of `F'/X'/B'` to `B'`. -/
@[reassoc (attr := simp)]
theorem canonicalBaseChangedQuotSitePresheafIso_hom_snd :
    (D.canonicalBaseChangedQuotSitePresheafIso p).hom ≫ Limits.pullback.snd _ _ =
      (D.canonicalBaseChanged p).quotSitePresheafToBase :=
  IsPullback.isoPullback_hom_snd _

/-- **Stacks 08IT for the Quot presheaf, the triangle over `B'`.**  The canonical morphism from
the Quot presheaf of `F'/X'/B'` to `B'` is the identification with the fibre product followed
by its second projection. -/
theorem quotSitePresheafToBase_canonicalBaseChanged :
    (D.canonicalBaseChanged p).quotSitePresheafToBase =
      (D.canonicalBaseChangedQuotSitePresheafIso p).hom ≫ Limits.pullback.snd _ _ :=
  (D.canonicalBaseChangedQuotSitePresheafIso_hom_snd p).symm

/-- **The sections of the Quot presheaf of `F'/X'/B'`, objectwise.**  Over a scheme `T` of the
site, a quotient of `F'/X'/B'` is the same as a morphism `b' : T ⟶ B'` together with a quotient
of `F/X/B` over `T` lying over `b' ≫ p`. -/
def canonicalBaseChangedQuotSitePresheafObjEquiv (T : (BigFppfOver B S hS)ᵒᵖ) :
    (D.canonicalBaseChanged p).quotSitePresheaf.obj T ≃
      {bx : ((schemeSpaceFunctor B S hS).obj T.unop ⟶ Y') × QuotFamilyOver D T.unop //
        bx.2.toBase = bx.1 ≫ p} :=
  Equiv.ofBijective (fun y ↦ ⟨(y.toBase, y.ofCanonicalBaseChanged), rfl⟩)
    ⟨fun y₁ y₂ h ↦ D.canonicalBaseChangedQuotSitePresheafHom_injective p
        (congrArg (fun bx ↦ bx.1.2) h) (congrArg (fun bx ↦ bx.1.1) h),
      fun ⟨⟨b', x⟩, hx⟩ ↦ by
        obtain ⟨y, hy, hyb⟩ := D.exists_ofCanonicalBaseChanged_eq p b' x hx
        exact ⟨y, Subtype.ext (Prod.ext hyb hy)⟩⟩

/-- The objectwise equivalence sends a quotient `y` of `F'/X'/B'` to the morphism it lies over
together with `y` read as a quotient of `F/X/B`. -/
@[simp]
theorem canonicalBaseChangedQuotSitePresheafObjEquiv_apply (T : (BigFppfOver B S hS)ᵒᵖ)
    (y : (D.canonicalBaseChanged p).quotSitePresheaf.obj T) :
    (D.canonicalBaseChangedQuotSitePresheafObjEquiv p T y).1 =
      (y.toBase, y.ofCanonicalBaseChanged) :=
  rfl

/-- **The sections of the fibre product, objectwise.**  Over a scheme `T` of the site, a section
of the fibre product of the Quot presheaf of `F/X/B` and of `B'` over `B` is a morphism
`b' : T ⟶ B'` together with a quotient of `F/X/B` over `T` lying over `b' ≫ p`. -/
def canonicalBaseChangedQuotSitePullbackObjEquiv (T : (BigFppfOver B S hS)ᵒᵖ) :
    (Limits.pullback D.quotSitePresheafToBase
        (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u})).obj T ≃
      {bx : ((schemeSpaceFunctor B S hS).obj T.unop ⟶ Y') × QuotFamilyOver D T.unop //
        bx.2.toBase = bx.1 ≫ p} :=
  ((D.canonicalBaseChangedQuotSitePresheafIso p).app T).symm.toEquiv.trans
    (D.canonicalBaseChangedQuotSitePresheafObjEquiv p T)

/-- If `e.hom ≫ g = k` for an isomorphism `e` of presheaves, then `k` evaluated at `e.inv w` is `g`
evaluated at `w`. -/
private theorem iso_inv_app_apply_comp {C : Type*} [Category C] {P Q R : Cᵒᵖ ⥤ Type (u + 1)}
    (e : P ≅ Q) {g : Q ⟶ R} {k : P ⟶ R} (h : e.hom ≫ g = k) (T : Cᵒᵖ) (w : Q.obj T) :
    k.app T (e.inv.app T w) = g.app T w := by
  rw [← h]
  simp

/-- Under the objectwise description, the first projection of the fibre product is the quotient
of `F/X/B`. -/
theorem canonicalBaseChangedQuotSitePullbackObjEquiv_fst (T : (BigFppfOver B S hS)ᵒᵖ)
    (w : (Limits.pullback D.quotSitePresheafToBase
        (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u})).obj T) :
    (D.canonicalBaseChangedQuotSitePullbackObjEquiv p T w).1.2 =
      (Limits.pullback.fst D.quotSitePresheafToBase
        (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u})).app T w := by
  exact iso_inv_app_apply_comp _ (D.canonicalBaseChangedQuotSitePresheafIso_hom_fst p) T w

/-- Under the objectwise description, the second projection of the fibre product is the point of
`B'` corresponding to the morphism `b' : T ⟶ B'`. -/
theorem canonicalBaseChangedQuotSitePullbackObjEquiv_snd (T : (BigFppfOver B S hS)ᵒᵖ)
    (w : (Limits.pullback D.quotSitePresheafToBase
        (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u})).obj T) :
    ULift.up (yonedaEquiv (D.canonicalBaseChangedQuotSitePullbackObjEquiv p T w).1.1.hom) =
      (Limits.pullback.snd D.quotSitePresheafToBase
        (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u})).app T w := by
  exact iso_inv_app_apply_comp _ (D.canonicalBaseChangedQuotSitePresheafIso_hom_snd p) T w

end QuotSituation

end AlgebraicGeometry.Space

end
