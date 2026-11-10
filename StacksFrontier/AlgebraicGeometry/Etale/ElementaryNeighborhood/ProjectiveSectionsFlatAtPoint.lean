module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ShrinkingToBasicOpen
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.RingTheory.Flat.DevissageLocalizeAwayProjective
import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.RingTheory.AdicCompletion.ShortExact

/-!
# Projective sections from flatness at a single point

Stacks Tag 05ID: let `f : X ⟶ S` be locally of finite presentation, let `F` be a quasi-coherent
`𝒪_X`-module of finite presentation and let `x` be a point of `X` at which `F` is flat over `S`.
Then there is a commutative square of pointed schemes
```
  (X, x) ← (X', x')
    ↓         ↓
  (S, s) ← (S', s')
```
whose horizontal arrows are elementary étale neighbourhoods, with `X'` and `S'` affine, such that
`Γ(X', g^*F)` is a projective `Γ(S', 𝒪_{S'})`-module.

The proof has three moves. Openness of the flat locus (Tag 0399) replaces `X` by the open
subscheme on which `F` is flat over `S` everywhere; Proposition 05HR together with Remark 05I0
produces an affine elementary étale square over which the global sections of the pullback of `F`
acquire a complete dévissage at the prime belonging to the distinguished point; and Lemma 05IB
over a general base turns that dévissage, together with flatness of those sections, into
projectivity after inverting one global function `a` on the new base which does not vanish at the
distinguished point. Shrinking the square to the basic opens of `a` and of its pullback restores
all the data of the square and identifies the localized sections with the sections there.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.flat_globalSections_of_isFlatOver`: for an affine square of étale
  neighbourhoods over `f`, flatness of `F` over `S` at every point of `X` makes the global
  sections of the pullback of `F` flat over the global functions on the lower neighbourhood.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`:
  **Tag 05ID**.

## Implementation notes

The prime at which the dévissage sits has to be the one belonging to the distinguished point of
the upper neighbourhood: the element Lemma 05IB produces lies outside its contraction to the
base, and that is what makes the element invertible at the distinguished point of the lower
neighbourhood, hence the shrinking possible.

Replacing `X` by the flat locus changes the module from `F` to its pullback, so the sections
appearing in the conclusion are compared with those of the pullback through
`AlgebraicGeometry.Scheme.Modules.pullbackComp`; the comparison is linear over the functions on
the new base because it is a morphism of sheaves of modules on the upper neighbourhood.

## References

* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
* [Stacks Project, Tag 05IB](https://stacks.math.columbia.edu/tag/05IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- An endomorphism of a sheaf of modules equal to the identity acts trivially on global
sections. -/
private theorem app_top_apply_of_eq_id {Y : Scheme.{u}} {M : Y.Modules} {ψ : M ⟶ M} (h : ψ = 𝟙 M)
    (t : Γ(M, (⊤ : Y.Opens))) : (ψ.app ⊤).hom t = t := by
  subst h
  simp

/-- An isomorphism of sheaves of modules on a scheme is an isomorphism of their global sections,
linear over any ring acting on both of them through the global functions on that scheme. -/
private def globalSectionsEquivOfIso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) {R : Type*}
    [CommRing R] (φ : R →+* Γ(Y, ⊤)) :
    letI : Module R Γ(M, (⊤ : Y.Opens)) := Module.compHom _ φ
    letI : Module R Γ(N, (⊤ : Y.Opens)) := Module.compHom _ φ
    Γ(M, (⊤ : Y.Opens)) ≃ₗ[R] Γ(N, (⊤ : Y.Opens)) :=
  letI : Module R Γ(M, (⊤ : Y.Opens)) := Module.compHom _ φ
  letI : Module R Γ(N, (⊤ : Y.Opens)) := Module.compHom _ φ
  { toFun := (e.hom.app ⊤).hom
    invFun := (e.inv.app ⊤).hom
    map_add' := map_add _
    map_smul' := fun r t => Scheme.Modules.Hom.app_smul e.hom (φ r) t
    left_inv := fun t => app_top_apply_of_eq_id e.hom_inv_id t
    right_inv := fun t => app_top_apply_of_eq_id e.inv_hom_id t }

/-- Projectivity of the global sections of a sheaf of modules on a scheme, over a ring acting
through the global functions, depends only on its isomorphism class. -/
private theorem projective_globalSections_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    {R : Type*} [CommRing R] (φ : R →+* Γ(Y, ⊤))
    (hM : letI : Module R Γ(M, (⊤ : Y.Opens)) := Module.compHom _ φ
      Module.Projective R Γ(M, (⊤ : Y.Opens))) :
    letI : Module R Γ(N, (⊤ : Y.Opens)) := Module.compHom _ φ
    Module.Projective R Γ(N, (⊤ : Y.Opens)) :=
  let : Module R Γ(M, (⊤ : Y.Opens)) := Module.compHom _ φ
  let : Module R Γ(N, (⊤ : Y.Opens)) := Module.compHom _ φ
  let := hM
  Module.Projective.of_equiv' (globalSectionsEquivOfIso e φ)

/-- For an affine square of étale neighbourhoods over `f`, a quasi-coherent module which is flat
over `S` at every point of `X` has the global sections of its pullback to the upper neighbourhood
flat over the global functions on the lower one.

Flatness over `S` of the pullback is flatness of `F` at the image point, the structure morphism of
an étale neighbourhood being flat, and flatness over `S` may be traded for flatness over the étale
base `V` by Stacks 05B9; on a pair of affine opens, flatness over the base is flatness of the
module of sections by Stacks 01U4. -/
theorem flat_globalSections_of_isFlatOver {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme)
    (hsq : h ≫ V.toBase = U.toBase ≫ f) [IsAffine U.scheme] [IsAffine V.scheme]
    (F : X.Modules) [F.IsQuasicoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    letI : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
      Module.compHom _ h.appTop.hom
    Module.Flat Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) := by
  have hGq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := inferInstance
  have hflatG : IsFlatOver h.toLRSHom.toShHom ((Scheme.Modules.pullback U.toBase).obj F) := by
    intro y
    have h₁ : IsFlatOverAt (U.toBase ≫ f).toLRSHom.toShHom
        ((Scheme.Modules.pullback U.toBase).obj F) y :=
      (isFlatOverAt_iff_modulePullback_isFlatOverAt U.toBase f F y
        (Flat.stalkMap U.toBase y)).mp (hflat (U.toBase y))
    rw [← hsq] at h₁
    exact (isFlatOverAt_comp_iff_of_etale h V.toBase
      ((Scheme.Modules.pullback U.toBase).obj F) y).mp h₁
  have happ : h.appTop = h.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app h).symm
  have hout := (isFlatOver_tfae h ((Scheme.Modules.pullback U.toBase).obj F)).out 1 2
  have hsec := hout.mp hflatG ⊤ (isAffineOpen_top U.scheme) ⊤ (isAffineOpen_top V.scheme) le_top
  rw [← happ] at hsec
  exact hsec

/-- Projectivity of the global sections after inverting a function on the base survives being
read on the shrunken square: the sections of the pullback of `F` to the basic open of `h^♯ a` are
the localization away from `a` of the sections of the pullback to the whole neighbourhood, and the
functions on the basic open of `a` are the localization of the functions on the base. -/
private theorem projective_sections_restrictBasicOpen {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    {V : EtaleNeighborhood S (f x)} {U : EtaleNeighborhood X x}
    [IsAffine U.scheme] [IsAffine V.scheme] (h : U.scheme ⟶ V.scheme) (F : X.Modules)
    [((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent]
    (a : Γ(V.scheme, ⊤)) (ha : V.point ∈ V.scheme.basicOpen a)
    (hproj :
      letI : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
        Module.compHom _ h.appTop.hom
      Module.Projective (Localization.Away a)
        (LocalizedModule (Submonoid.powers a)
          Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤))) :
    letI : Module Γ((V.scheme.basicOpen a).toScheme, ⊤)
        Γ((Scheme.Modules.pullback
          ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
      Module.compHom _ (restrictBasicOpenHom h a).appTop.hom
    Module.Projective Γ((V.scheme.basicOpen a).toScheme, ⊤)
      Γ((Scheme.Modules.pullback
        ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) := by
  let : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
  let : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    Module.compHom _ h.appTop.hom
  let := modulePullbackBasicOpenSections U.toBase F (h.appTop.hom a)
  let : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback
      ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
    Module.compHom _ ((U.scheme.basicOpen (h.appTop.hom a)).ι.appTop.hom.comp h.appTop.hom)
  have : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
      Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
      Γ((Scheme.Modules.pullback
        ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hψ : IsLocalizedModule.Away a
      ((pullbackBasicOpenSectionsMap U.toBase F (h.appTop.hom a)).restrictScalars
        Γ(V.scheme, ⊤)) :=
    isLocalizedModule_pullbackBasicOpenSectionsMap_base f h F a
  let : Algebra Γ(V.scheme, ⊤) Γ((V.scheme.basicOpen a).toScheme, ⊤) :=
    (V.scheme.basicOpen a).ι.appTop.hom.toAlgebra
  have hlocR : IsLocalization.Away a Γ((V.scheme.basicOpen a).toScheme, ⊤) :=
    V.isLocalization_away_restrictOpen_basicOpen a ha
  let : Module Γ((V.scheme.basicOpen a).toScheme, ⊤) Γ((Scheme.Modules.pullback
      ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
    Module.compHom _ (restrictBasicOpenHom h a).appTop.hom
  have htowerN : IsScalarTower Γ(V.scheme, ⊤) Γ((V.scheme.basicOpen a).toScheme, ⊤)
      Γ((Scheme.Modules.pullback
        ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun r t =>
      congrArg (fun z => z • t)
        (congrArg (fun φ : Γ(V.scheme, ⊤) ⟶ Γ((U.scheme.basicOpen (h.appTop.hom a)).toScheme, ⊤) =>
          φ.hom r) (appTop_comp_restrictBasicOpenHom_appTop h a))
  let ε : Γ((V.scheme.basicOpen a).toScheme, ⊤) ≃+* Localization.Away a :=
    (IsLocalization.algEquiv (Submonoid.powers a) Γ((V.scheme.basicOpen a).toScheme, ⊤)
      (Localization.Away a)).toRingEquiv
  let : Module Γ((V.scheme.basicOpen a).toScheme, ⊤) (LocalizedModule (Submonoid.powers a)
      Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤)) :=
    Module.compHom _ (ε : Γ((V.scheme.basicOpen a).toScheme, ⊤) →+* Localization.Away a)
  have htowerL : IsScalarTower Γ(V.scheme, ⊤) Γ((V.scheme.basicOpen a).toScheme, ⊤)
      (LocalizedModule (Submonoid.powers a)
        Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤)) :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change ε (algebraMap Γ(V.scheme, ⊤) Γ((V.scheme.basicOpen a).toScheme, ⊤) r) • m = r • m
      rw [show ε (algebraMap Γ(V.scheme, ⊤) Γ((V.scheme.basicOpen a).toScheme, ⊤) r) =
          algebraMap Γ(V.scheme, ⊤) (Localization.Away a) r from
        (IsLocalization.algEquiv (Submonoid.powers a)
          Γ((V.scheme.basicOpen a).toScheme, ⊤) (Localization.Away a)).commutes r,
        IsScalarTower.algebraMap_smul]
  have : Module.Projective (Localization.Away a) (LocalizedModule (Submonoid.powers a)
      Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤)) := hproj
  have : Module.Projective Γ((V.scheme.basicOpen a).toScheme, ⊤)
      (LocalizedModule (Submonoid.powers a)
        Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤)) :=
    Stacks.AdicCompletion.SplitShortExact.projective_of_ringEquiv ε.symm (AddEquiv.refl _)
      (fun c x => congrArg (fun r => r • x) (ε.apply_symm_apply c).symm) ‹_›
  exact Module.Projective.of_equiv'
    (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers a)
      Γ((V.scheme.basicOpen a).toScheme, ⊤)
      (IsLocalizedModule.linearEquiv (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a)
          Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤))
        ((pullbackBasicOpenSectionsMap U.toBase F (h.appTop.hom a)).restrictScalars
          Γ(V.scheme, ⊤))))

/-- **Stacks Project, Tag 05ID.** A finitely presented quasi-coherent module which is flat over
the base at a point has projective global sections after compatible affine elementary étale
localization of the source and of the base.

Openness of the flat locus (Tag 0399) replaces `X` by the open subscheme on which `F` is flat over
`S`; Proposition 05HR and Remark 05I0 then produce an affine elementary étale square carrying a
complete dévissage of the global sections at the prime of the distinguished point, and Lemma 05IB
over a general base makes those sections projective after inverting a global function on the new
base which does not vanish at the distinguished point. Shrinking the square to the basic opens of
that function and of its pullback gives the square of the conclusion. -/
@[stacks 05ID]
theorem exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFinitePresentation f] [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (V : EtaleNeighborhood S (f x))
      (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme),
      V.IsElementary ∧ U.IsElementary ∧
        (h ≫ V.toBase = U.toBase ≫ f) ∧ (h U.point = V.point) ∧
        IsAffine U.scheme ∧ IsAffine V.scheme ∧
        (let M := (Scheme.Modules.pullback U.toBase).obj F
         letI : Module Γ(V.scheme, ⊤) Γ(M, ⊤) :=
           Module.compHom Γ(M, ⊤) h.appTop.hom
         Module.Projective Γ(V.scheme, ⊤) Γ(M, ⊤)) := by
  have hFt : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  -- Shrink `X` to the open locus on which `F` is flat over `S`.
  let O : X.Opens := ⟨{y : X | IsFlatOverAt f.toLRSHom.toShHom F y},
    isOpen_setOf_flatOverAt f F⟩
  have hxO : x ∈ O := hflat
  let P : EtaleNeighborhood X x := EtaleNeighborhood.ofEtale O.ι ⟨x, hxO⟩
  have hPel : P.IsElementary :=
    EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion O.ι ⟨x, hxO⟩
  let F' : O.toScheme.Modules := (Scheme.Modules.pullback O.ι).obj F
  have hF't : F'.IsFiniteType := SheafOfModules.pullback_isFiniteType O.ι.toLRSHom.toShHom F
  have hflat' : IsFlatOver (O.ι ≫ f).toLRSHom.toShHom F' := fun y =>
    (isFlatOverAt_iff_modulePullback_isFlatOverAt O.ι f F y (Flat.stalkMap O.ι y)).mp y.2
  obtain ⟨V, U₀, h, hVel, hU₀el, hsq, hpt, hU₀aff, hVaff, hfth, hGq, hGt, hD⟩ :=
    exists_affine_elementaryEtaleNeighborhood_completeDevissageAt_globalSections
      (O.ι ≫ f) F' ⟨x, hxO⟩
  let : IsAffine U₀.scheme := hU₀aff
  let : IsAffine V.scheme := hVaff
  let : Algebra Γ(V.scheme, ⊤) Γ(U₀.scheme, ⊤) := h.appTop.hom.toAlgebra
  let : Algebra.FiniteType Γ(V.scheme, ⊤) Γ(U₀.scheme, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) h hfth
  let : ((Scheme.Modules.pullback U₀.toBase).obj F').IsQuasicoherent := hGq
  let : ((Scheme.Modules.pullback U₀.toBase).obj F').IsFiniteType := hGt
  let : Module.Finite Γ(U₀.scheme, ⊤)
      Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections _ (isAffineOpen_top U₀.scheme)
  let : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) :=
    Module.compHom _ h.appTop.hom
  let : (U₀.scheme.isoSpec.hom U₀.point).asIdeal.IsPrime :=
    (U₀.scheme.isoSpec.hom U₀.point).isPrime
  obtain ⟨D⟩ := hD
  -- Sections of the pullback of `F'` are sections of the pullback of `F`.
  have hcomp : ∀ {W : Scheme.{u}} (k : W ⟶ O.toScheme),
      (Scheme.Modules.pullback k).obj F' ≅ (Scheme.Modules.pullback (k ≫ O.ι)).obj F :=
    fun k => (Scheme.Modules.pullbackComp k O.ι).app F
  cases D with
  | empty hzero =>
    refine ⟨V, P.comp U₀, h, hVel, hPel.comp hU₀el, ?_, hpt, hU₀aff, hVaff, ?_⟩
    · change h ≫ V.toBase = (U₀.toBase ≫ O.ι) ≫ f
      rw [Category.assoc]
      exact hsq
    · have hsub : Subsingleton Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) := hzero
      have : Module.Free Γ(V.scheme, ⊤)
          Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) :=
        Module.Free.of_subsingleton _ _
      have hproj0 : Module.Projective Γ(V.scheme, ⊤)
          Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) := Module.Projective.of_free
      exact projective_globalSections_of_iso (hcomp U₀.toBase) h.appTop.hom hproj0
  | nonempty E =>
    let : Algebra.FinitePresentation Γ(V.scheme, ⊤) Γ(U₀.scheme, ⊤) :=
      EtaleNeighborhood.algebraFinitePresentation_globalSections (O.ι ≫ f) V U₀ h hsq
    let : ((Scheme.Modules.pullback U₀.toBase).obj F').IsFinitePresentation := inferInstance
    let : Module.FinitePresentation Γ(U₀.scheme, ⊤)
        Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) :=
      Stacks.AlgebraicGeometry.ModuleLimits.finitePresentation_sectionsTop _
    let : IsScalarTower Γ(V.scheme, ⊤) Γ(U₀.scheme, ⊤)
        Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : Module.Flat Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U₀.toBase).obj F', ⊤) :=
      flat_globalSections_of_isFlatOver (O.ι ≫ f) V U₀ h hsq F' hflat'
    obtain ⟨a, ha, hproj⟩ := E.exists_away_projective
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_under, RingHom.algebraMap_toAlgebra] at ha
    have hbU : U₀.point ∈ U₀.scheme.basicOpen (h.appTop.hom a) := by
      rw [← U₀.scheme.map_PrimeSpectrum_basicOpen_of_affine (h.appTop.hom a)]
      exact ha
    have hpre : U₀.point ∈ h ⁻¹ᵁ (V.scheme.basicOpen a) := by
      rw [Scheme.preimage_basicOpen_top h a]
      exact hbU
    have hbV : V.point ∈ V.scheme.basicOpen a := by
      rw [← hpt]
      exact hpre
    obtain ⟨hV'el, hU₀'el, hV'aff, hU₀'aff, hsq', hpt'⟩ :=
      restrictBasicOpen_isAffineElementaryEtaleSquare (f := O.ι ≫ f) hVel hU₀el h hsq hpt a hbV
    have hprojN := projective_sections_restrictBasicOpen (O.ι ≫ f) h F' a hbV hproj
    refine ⟨V.restrictOpen (V.scheme.basicOpen a) hbV,
      P.comp (U₀.restrictOpen (U₀.scheme.basicOpen (h.appTop.hom a)) hbU),
      restrictBasicOpenHom h a, hV'el, hPel.comp hU₀'el, ?_, hpt', hU₀'aff, hV'aff, ?_⟩
    · change restrictBasicOpenHom h a ≫ (V.scheme.basicOpen a).ι ≫ V.toBase =
        (((U₀.scheme.basicOpen (h.appTop.hom a)).ι ≫ U₀.toBase) ≫ O.ι) ≫ f
      rw [Category.assoc]
      exact hsq'
    · exact projective_globalSections_of_iso
        (hcomp ((U₀.scheme.basicOpen (h.appTop.hom a)).ι ≫ U₀.toBase))
        (restrictBasicOpenHom h a).appTop.hom hprojN

end AlgebraicGeometry

end
