module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsFlatBaseChangeSpan
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSectionAlongComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkPointHigherDirectImageVanishing

/-!
# From sections over `X ×_Y Spec 𝒪_{Y,y}` to sections over a neighbourhood of the fibre

Let `Y` be a scheme of the big fppf site, `y ∈ Y`, `W ∋ y` an affine open, `f : X ⟶ Y`
quasi-compact and quasi-separated, and `𝒢` a quasi-coherent `𝒪_X`-module. Write `X_W` for the
preimage of `W` and `X' = X_W ×_W Spec 𝒪_{Y,y}`. If a global section `t` of `𝒢` over the fibre
`X_y = U` is the restriction of a global section of `𝒢` over `X'`, then it is the restriction
of a global section of `𝒢` over the preimage `X_V` of some open neighbourhood `V ⊆ W` of `y`.

## Main definitions

* `AlgebraicGeometry.Space.sectionPullback`: the inverse image of a global section along a
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.sectionPullbackₛₗ`: `AlgebraicGeometry.Space.sectionPullback` as a
  semilinear map.

## Main results

* `AlgebraicGeometry.Space.exists_open_restrictSectionAlong_eq_of_stalkBaseChange`: a section
  over the fibre that extends to `X'` extends to the preimage `X_V` of a neighbourhood `V` of `y`.

## References

* [Stacks Project, Tag 0D39](https://stacks.math.columbia.edu/tag/0D39)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section

variable (Y : BigFppfOver B S hS)
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  {y : (BigFppfOver.toScheme B S hS).obj Y} (W : ((BigFppfOver.toScheme B S hS).obj Y).Opens)
  (hy : y ∈ W)

/-- `Spec 𝒪_{Y,y} ⟶ W` is flat, read as a morphism of algebraic spaces. -/
theorem isFlat_stalkPointToOpen :
    IsFlat B S hS (yoneda.map (stalkPointToOpen Y W hy)) :=
  holdsOnEveryEtaleChart_yoneda_map B S hS
    AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget (stalkPointToOpen Y W hy)
    (by
      show Flat (W.fromSpecStalkOfMem y hy)
      have h1 : Flat (W.fromSpecStalkOfMem y hy ≫ W.ι) := by
        rw [Scheme.Opens.fromSpecStalkOfMem_ι W y hy]
        exact AlgebraicGeometry.flat_fromSpecStalk _ y
      exact (MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
        (P := @Flat)).of_postcomp _ W.ι (inferInstanceAs (Mono W.ι)) h1)

end

/-- The inverse of `AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`. -/
def modulePullbackCompIsoInvApp {X Y Z : AlgebraicSpaces B S hS} (k : Z ⟶ Y) (p : Y ⟶ X)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (k ≫ p)).obj G ⟶
      (modulePullback B S hS k).obj ((modulePullback B S hS p).obj G) :=
  (modulePullbackCompIso B S hS k p).inv.app G

/-- `AlgebraicGeometry.Space.modulePullbackCompIsoInvApp` followed by
`AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`, on global sections, is the identity. -/
theorem modulePullbackCompIsoHomApp_modulePullbackCompIsoInvApp_apply
    {X Y Z : AlgebraicSpaces B S hS} (k : Z ⟶ Y) (p : Y ⟶ X) (G : Modules.{u, u} B S hS X.1 X.2)
    (s : spaceModuleSections Z ((modulePullback B S hS (k ≫ p)).obj G)) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map
          (modulePullbackCompIsoHomApp k p G)).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map
          (modulePullbackCompIsoInvApp k p G)).hom s) = s := by
  rw [← globalSectionsFunctor_map_comp_apply]
  have e : modulePullbackCompIsoInvApp k p G ≫ modulePullbackCompIsoHomApp k p G = 𝟙 _ :=
    (modulePullbackCompIso B S hS k p).inv_hom_id_app G
  rw [e, CategoryTheory.Functor.map_id]
  rfl

/-! ### The inverse image of global sections as a semilinear map -/

/-- The inverse image of a global section along `k : Z' ⟶ Z`, as an element of the module of
global sections of `k^*𝓜` over `Γ(Z', 𝒪)`. -/
def sectionPullback {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
    (σ : spaceModuleSections Z M) : spaceModuleSections Z' ((modulePullback B S hS k).obj M) :=
  (globalSectionsPullbackMap B S hS k M).hom σ

/-- `AlgebraicGeometry.Space.sectionPullback` is additive. -/
theorem sectionPullback_add {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (σ τ : spaceModuleSections Z M) :
    sectionPullback k M (σ + τ) = sectionPullback k M σ + sectionPullback k M τ :=
  map_add (globalSectionsPullbackMap B S hS k M).hom σ τ

/-- `AlgebraicGeometry.Space.sectionPullback` is semilinear over `Γ(Z, 𝒪) ⟶ Γ(Z', 𝒪)`. -/
theorem sectionPullback_smul {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2)
    (a : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj)
    (σ : spaceModuleSections Z M) :
    sectionPullback k M (a • σ) = globalSectionsRingHomSite B S hS k a • sectionPullback k M σ :=
  map_smul (globalSectionsPullbackMap B S hS k M).hom a σ

/-- `AlgebraicGeometry.Space.sectionPullback` as a semilinear map. -/
def sectionPullbackₛₗ {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    spaceModuleSections Z M →ₛₗ[globalSectionsRingHomSite B S hS k]
      spaceModuleSections Z' ((modulePullback B S hS k).obj M) where
  toFun := sectionPullback k M
  map_add' := sectionPullback_add k M
  map_smul' := sectionPullback_smul k M

/-- The inverse image along `a : Z' ⟶ V` of a combination `Σ rᵢ k^*σᵢ` of sections pulled back
along `k : V ⟶ X_W` is, read on `(a ≫ k)^*N`, the combination `Σ a^*(rᵢ) (a ≫ k)^*σᵢ`. -/
theorem modulePullbackCompIsoHomApp_sectionPullback_sum {Z' V XW : AlgebraicSpaces B S hS}
    (a : Z' ⟶ V) (k : V ⟶ XW) (N : Modules.{u, u} B S hS XW.1 XW.2) {ι : Type*} (s : Finset ι)
    (r : ι → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O).obj)
    (σ : ι → spaceModuleSections XW N) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
          (modulePullbackCompIsoHomApp a k N)).hom
        (sectionPullback a ((modulePullback B S hS k).obj N)
          (∑ i ∈ s, r i • sectionPullback k N (σ i))) =
      ∑ i ∈ s, globalSectionsRingHomSite B S hS a (r i) • sectionPullback (a ≫ k) N (σ i) := by
  have h₁ := map_sum (sectionPullbackₛₗ a ((modulePullback B S hS k).obj N))
    (fun i => r i • sectionPullback k N (σ i)) s
  change sectionPullback a ((modulePullback B S hS k).obj N)
    (∑ i ∈ s, r i • sectionPullback k N (σ i)) = _ at h₁
  rw [h₁, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
          (modulePullbackCompIsoHomApp a k N)).hom
      (sectionPullback a ((modulePullback B S hS k).obj N) (r i • sectionPullback k N (σ i))) = _
  rw [sectionPullback_smul, map_smul]
  exact congrArg (globalSectionsRingHomSite B S hS a (r i) • ·)
    (modulePullbackCompIsoHomApp_globalSectionsPullbackMap a k N (σ i))

/-- The restriction to `U` of a combination of sections pulled back along `k : V ⟶ X_W` is the
combination, with the coefficients restricted to `U`, of their pullbacks along the composite
`U ⟶ X_W`. -/
theorem restrictSectionAlong_sum_sectionPullback {X XW V : AlgebraicSpaces B S hS}
    (k : V ⟶ XW) (pW : XW ⟶ X) (pV : V ⟶ X) (hk : k ≫ pW = pV) (U : BigFppfOver B S hS)
    (j : yoneda.obj U ⟶ V.1) (p : yoneda.obj U ⟶ X.1) (h : j ≫ pV.hom = p)
    (G : Modules.{u, u} B S hS X.1 X.2) {ι : Type*} (s : Finset ι)
    (r : ι → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O).obj)
    (σ : ι → spaceModuleSections XW ((modulePullback B S hS pW).obj G))
    (h' : ((representedPointHom U j) ≫ k) ≫ pW =
      ObjectProperty.homMk p) :
    restrictSectionAlong pV U j p h G ((spaceModuleSectionsPullbackCongr hk G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)).map
            (modulePullbackCompIsoHomApp k pW G)).hom
          (∑ i ∈ s, r i • sectionPullback k ((modulePullback B S hS pW).obj G) (σ i)))) =
      (spaceModuleSectionsPullbackCongr h' G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
            (representedAlgebraicSpace B S hS U).2).O)).map
            (modulePullbackCompIsoHomApp
              ((representedPointHom U j) ≫ k) pW G)).hom
          (∑ i ∈ s, globalSectionsRingHomSite B S hS
              (representedPointHom U j) (r i) •
            sectionPullback ((representedPointHom U j) ≫ k)
              ((modulePullback B S hS pW).obj G) (σ i))) :=
  (restrictSectionAlong_modulePullbackCompIsoHomApp k pW pV hk U j p h G _ h').trans
    (congrArg (fun z => (spaceModuleSectionsPullbackCongr h' G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
            (representedAlgebraicSpace B S hS U).2).O)).map
            (modulePullbackCompIsoHomApp
              ((representedPointHom U j) ≫ k) pW G)).hom z))
      (modulePullbackCompIsoHomApp_sectionPullback_sum
        (representedPointHom U j) k
        ((modulePullback B S hS pW).obj G) s r σ))

/-- `AlgebraicGeometry.Space.restrictSectionAlong_sum_sectionPullback`, with the composite
`U ⟶ X_W` replaced by any morphism equal to it. -/
theorem restrictSectionAlong_sum_sectionPullback_of_eq {X XW V : AlgebraicSpaces B S hS}
    (k : V ⟶ XW) (pW : XW ⟶ X) (pV : V ⟶ X) (hk : k ≫ pW = pV) (U : BigFppfOver B S hS)
    (j : yoneda.obj U ⟶ V.1) (p : yoneda.obj U ⟶ X.1) (h : j ≫ pV.hom = p)
    (G : Modules.{u, u} B S hS X.1 X.2) {ι : Type*} (s : Finset ι)
    (r : ι → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O).obj)
    (σ : ι → spaceModuleSections XW ((modulePullback B S hS pW).obj G))
    (ρ : representedAlgebraicSpace B S hS U ⟶ XW)
    (hρ : (representedPointHom U j) ≫ k = ρ)
    (h' : ρ ≫ pW = ObjectProperty.homMk p) :
    restrictSectionAlong pV U j p h G ((spaceModuleSectionsPullbackCongr hk G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)).map
            (modulePullbackCompIsoHomApp k pW G)).hom
          (∑ i ∈ s, r i • sectionPullback k ((modulePullback B S hS pW).obj G) (σ i)))) =
      (spaceModuleSectionsPullbackCongr h' G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
            (representedAlgebraicSpace B S hS U).2).O)).map
            (modulePullbackCompIsoHomApp ρ pW G)).hom
          (∑ i ∈ s, globalSectionsRingHomSite B S hS
              (representedPointHom U j) (r i) •
            sectionPullback ρ ((modulePullback B S hS pW).obj G) (σ i))) := by
  subst hρ
  exact restrictSectionAlong_sum_sectionPullback k pW pV hk U j p h G s r σ h'

/-- Restricting to `U` combinations of pulled-back sections over `X_V` and over `X'` gives the
same section when the two morphisms `U ⟶ X_W` agree and so do the coefficients on `U`. -/
theorem restrictSectionAlong_sum_sectionPullback_eq {X XW XV X' : AlgebraicSpaces B S hS}
    (pW : XW ⟶ X) (k : XV ⟶ XW) (pV : XV ⟶ X) (hk : k ≫ pW = pV) (g' : X' ⟶ XW)
    (U : BigFppfOver B S hS) (jV : yoneda.obj U ⟶ XV.1) (p : yoneda.obj U ⟶ X.1)
    (hjV : jV ≫ pV.hom = p) (p' : yoneda.obj U ⟶ X'.1) (hp' : p' ≫ (g' ≫ pW).hom = p)
    (G : Modules.{u, u} B S hS X.1 X.2) {ι : Type*} (s : Finset ι)
    (σ : ι → spaceModuleSections XW ((modulePullback B S hS pW).obj G))
    (rV : ι → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O).obj)
    (rX : ι → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj)
    (hM : representedPointHom U jV ≫ k = representedPointHom U p' ≫ g')
    (hring : ∀ i ∈ s,
      globalSectionsRingHomSite B S hS (representedPointHom U jV) (rV i) =
        globalSectionsRingHomSite B S hS (representedPointHom U p') (rX i)) :
    restrictSectionAlong pV U jV p hjV G ((spaceModuleSectionsPullbackCongr hk G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O)).map
            (modulePullbackCompIsoHomApp k pW G)).hom
          (∑ i ∈ s, rV i • sectionPullback k ((modulePullback B S hS pW).obj G) (σ i)))) =
      restrictSectionAlong (g' ≫ pW) U p' p hp' G
        ((spaceModuleSectionsPullbackCongr (rfl : g' ≫ pW = g' ≫ pW) G).hom
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).map
              (modulePullbackCompIsoHomApp g' pW G)).hom
            (∑ i ∈ s, rX i • sectionPullback g' ((modulePullback B S hS pW).obj G) (σ i)))) := by
  have hρp : ((representedPointHom U p') ≫ g') ≫ pW =
      ObjectProperty.homMk p := by
    rw [Category.assoc]
    exact ObjectProperty.hom_ext _ hp'
  refine (restrictSectionAlong_sum_sectionPullback_of_eq k pW pV hk U jV p hjV G s rV σ _ hM
    hρp).trans ?_
  refine Eq.trans ?_ (restrictSectionAlong_sum_sectionPullback_of_eq g' pW (g' ≫ pW) rfl U p' p hp'
    G s rX σ _ rfl hρp).symm
  refine congrArg (fun z => (spaceModuleSectionsPullbackCongr hρp G).hom
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
        (representedAlgebraicSpace B S hS U).2).O)).map
        (modulePullbackCompIsoHomApp _ pW G)).hom z)) ?_
  exact Finset.sum_congr rfl fun i hi => by rw [hring i hi]

section Lift

variable {Y : BigFppfOver B S hS}
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  {y : (BigFppfOver.toScheme B S hS).obj Y} {W : ((BigFppfOver.toScheme B S hS).obj Y).Opens}
  (hy : y ∈ W) (hWaff : IsAffineOpen W)
  {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
  (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
  (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
  {XW : AlgebraicSpaces B S hS} (pW : XW ⟶ X)
  (fW : XW ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y W))
  (hW : IsPullback pW fW f (representedSpaceMap B S hS (openSiteObjectHom B S hS Y W)))
  {X' : AlgebraicSpaces B S hS} (g' : X' ⟶ XW)
  (f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y))
  (hX' : IsPullback g' f' fW (representedSpaceMap B S hS (stalkPointToOpen Y W hy)))
  (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) (p' : yoneda.obj U ⟶ X'.1)
  (hp' : p' ≫ (g' ≫ pW).hom = p)

include hy hW hX' in
/-- If a section `s₀` of `𝒢` over `X'` restricting to `t` on the fibre is, read on
`g'^*p_W^*𝒢`, a combination `Σ cᵢ σᵢ` of pullbacks of sections over `X_W` whose coefficients come
from functions `aᵢ` on an open `V ∋ y` inside `W`, then `t` is the restriction of a section of `𝒢`
over every `X_V`. -/
theorem exists_restrictSectionAlong_eq_of_coefficients
    (t : spaceModuleSections (representedAlgebraicSpace B S hS U)
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj G))
    (s₀ : spaceModuleSections X' ((modulePullback B S hS (g' ≫ pW)).obj G))
    (hs₀ : restrictSectionAlong (g' ≫ pW) U p' p hp' G s₀ = t)
    (s₁ : spaceModuleSections X'
      ((modulePullback B S hS g').obj ((modulePullback B S hS pW).obj G)))
    (hs₁₀ : ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).map
          (modulePullbackCompIsoHomApp g' pW G)).hom s₁ = s₀)
    (supp : Finset (spaceModuleSections XW ((modulePullback B S hS pW).obj G)))
    (cT : spaceModuleSections XW ((modulePullback B S hS pW).obj G) →
      RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
        (representedAlgebraicSpace B S hS (stalkPointObject Y y)).1
        (representedAlgebraicSpace B S hS (stalkPointObject Y y)).2).O).obj)
    (hs₁ : s₁ = ∑ σ ∈ supp, globalSectionsRingHomSite B S hS f' (cT σ) •
        sectionPullback g' ((modulePullback B S hS pW).obj G) σ)
    (V : ((BigFppfOver.toScheme B S hS).obj Y).Opens) (hVW : V ≤ W) (hyV : y ∈ V)
    (a : spaceModuleSections XW ((modulePullback B S hS pW).obj G) →
      RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
        (representedAlgebraicSpace B S hS (openSiteObject B S hS Y V)).1
        (representedAlgebraicSpace B S hS (openSiteObject B S hS Y V)).2).O).obj)
    (ha : ∀ σ ∈ supp, globalSectionsRingHomSite B S hS
      (representedSpaceMap B S hS (stalkPointToOpen Y V hyV)) (a σ) = cT σ) :
    ∀ ⦃XV : AlgebraicSpaces B S hS⦄ (pV : XV ⟶ X)
      (fV : XV ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y V)),
      IsPullback pV fV f
        (ObjectProperty.homMk (yoneda.map (openSiteObjectHom B S hS Y V))) →
      ∀ (jV : yoneda.obj U ⟶ XV.1) (h : jV ≫ pV.hom = p),
        ∃ s : spaceModuleSections XV ((modulePullback B S hS pV).obj G),
          restrictSectionAlong pV U jV p h G s = t := by
  intro XV pV fV hsqV jV hjV
  have hw : pV ≫ f = fV ≫ representedSpaceMap B S hS (openSiteObjectHom B S hS Y V) := hsqV.w
  have hcomm : pV ≫ f = (fV ≫ representedSpaceMap B S hS (openSiteObjectHomOfLE Y hVW)) ≫
      representedSpaceMap B S hS (openSiteObjectHom B S hS Y W) := by
    rw [Category.assoc, representedSpaceMap_comp B S hS, openSiteObjectHomOfLE_comp]
    exact hw
  obtain ⟨k, hk, hkf⟩ : ∃ k : XV ⟶ XW, k ≫ pW = pV ∧
      k ≫ fW = fV ≫ representedSpaceMap B S hS (openSiteObjectHomOfLE Y hVW) :=
    ⟨hW.lift pV _ hcomm, hW.lift_fst _ _ hcomm, hW.lift_snd _ _ hcomm⟩
  have hj : (representedPointHom U jV) ≫ pV =
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) :=
    ObjectProperty.hom_ext _ hjV
  have hq : (representedPointHom U p') ≫ (g' ≫ pW) =
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) :=
    ObjectProperty.hom_ext _ hp'
  have hU1 : (representedPointHom U jV) ≫ fV ≫
      representedSpaceMap B S hS (openSiteObjectHom B S hS Y V) =
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) ≫ f := by
    rw [← hw, ← Category.assoc, hj]
  have hU2 : (representedPointHom U p') ≫ f' ≫
      representedSpaceMap B S hS (stalkPointToOpen Y W hy) ≫
      representedSpaceMap B S hS (openSiteObjectHom B S hS Y W) =
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) ≫ f := by
    rw [← Category.assoc f', ← hX'.w, Category.assoc, ← hW.w, ← hq]
    simp only [Category.assoc]
  have hM1 : (representedPointHom U jV) ≫ fV =
      (representedPointHom U p') ≫ f' ≫ representedSpaceMap B S hS (stalkPointToOpen Y V hyV) := by
    refine representedSpaceMap_openSiteObjectHom_cancel Y ?_
    rw [Category.assoc, hU1]
    simp only [Category.assoc]
    rw [representedSpaceMap_comp B S hS, stalkPointToOpen_comp_openSiteObjectHom Y V hyV,
      ← stalkPointToOpen_comp_openSiteObjectHom Y W hy, ← representedSpaceMap_comp B S hS, hU2]
  have hM2 : (representedPointHom U jV) ≫ k = (representedPointHom U p') ≫ g' := by
    refine hW.hom_ext ?_ ?_
    · rw [Category.assoc, hk, hj, Category.assoc, hq]
    · rw [Category.assoc, hkf, Category.assoc, hX'.w]
      refine representedSpaceMap_openSiteObjectHom_cancel Y ?_
      simp only [Category.assoc]
      rw [representedSpaceMap_comp B S hS, openSiteObjectHomOfLE_comp, hU1, hU2]
  have h'V : ((representedPointHom U jV) ≫ k) ≫ pW =
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) := by
    rw [Category.assoc, hk, hj]
  have h'X : ((representedPointHom U p') ≫ g') ≫ pW =
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) := by
    rw [Category.assoc, hq]
  have hring : ∀ σ ∈ supp,
      globalSectionsRingHomSite B S hS (representedPointHom U jV)
          (globalSectionsRingHomSite B S hS fV (a σ)) =
        globalSectionsRingHomSite B S hS (representedPointHom U p')
          (globalSectionsRingHomSite B S hS f' (cT σ)) := by
    intro σ hσ
    have hc' : cT σ = globalSectionsRingHomSite B S hS
        (representedSpaceMap B S hS (stalkPointToOpen Y V hyV)) (a σ) := (ha σ hσ).symm
    have e1 := RingHom.congr_fun
      (globalSectionsRingHomSite_comp B S hS (representedPointHom U jV) fV) (a σ)
    have e2 := RingHom.congr_fun (globalSectionsRingHomSite_comp B S hS (representedPointHom U p')
      (f' ≫ representedSpaceMap B S hS (stalkPointToOpen Y V hyV))) (a σ)
    have e3 := RingHom.congr_fun (globalSectionsRingHomSite_comp B S hS f'
      (representedSpaceMap B S hS (stalkPointToOpen Y V hyV))) (a σ)
    refine (e1.symm.trans ((congrArg (fun φ => globalSectionsRingHomSite B S hS φ (a σ)) hM1).trans
      (e2.trans
        (congrArg (globalSectionsRingHomSite B S hS (representedPointHom U p')) e3)))).trans ?_
    exact congrArg (fun z => globalSectionsRingHomSite B S hS (representedPointHom U p')
      (globalSectionsRingHomSite B S hS f' z)) hc'.symm
  obtain ⟨rV, hrV⟩ : ∃ rV : spaceModuleSections XW ((modulePullback B S hS pW).obj G) →
      RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O).obj,
      ∀ σ, rV σ = globalSectionsRingHomSite B S hS fV (a σ) := ⟨_, fun _ => rfl⟩
  obtain ⟨rX, hrX⟩ : ∃ rX : spaceModuleSections XW ((modulePullback B S hS pW).obj G) →
      RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj,
      ∀ σ, rX σ = globalSectionsRingHomSite B S hS f' (cT σ) := ⟨_, fun _ => rfl⟩
  obtain ⟨σf, hσf⟩ : ∃ σf : spaceModuleSections XW ((modulePullback B S hS pW).obj G) →
      spaceModuleSections XW ((modulePullback B S hS pW).obj G), ∀ σ, σf σ = σ :=
    ⟨id, fun _ => rfl⟩
  have hring' : ∀ σ ∈ supp,
      globalSectionsRingHomSite B S hS (representedPointHom U jV) (rV σ) =
        globalSectionsRingHomSite B S hS (representedPointHom U p') (rX σ) := by
    intro σ hσ
    rw [hrV, hrX]
    exact hring σ hσ
  have hs₁' : s₁ = ∑ σ ∈ supp,
      rX σ • sectionPullback g' ((modulePullback B S hS pW).obj G) (σf σ) := by
    rw [hs₁]
    exact Finset.sum_congr rfl fun σ _ => by rw [hrX, hσf]
  refine ⟨(spaceModuleSectionsPullbackCongr hk G).hom
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O)).map
        (modulePullbackCompIsoHomApp k pW G)).hom
      (∑ σ ∈ supp, rV σ • sectionPullback k ((modulePullback B S hS pW).obj G) (σf σ))), ?_⟩
  have e0 : s₀ = (spaceModuleSectionsPullbackCongr (rfl : g' ≫ pW = g' ≫ pW) G).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).map
          (modulePullbackCompIsoHomApp g' pW G)).hom s₁) :=
    ((spaceModuleSectionsPullbackCongr_rfl_apply _ G _).trans hs₁₀).symm
  refine Eq.trans ?_ hs₀
  refine Eq.trans ?_ (congrArg (restrictSectionAlong (g' ≫ pW) U p' p hp' G) e0).symm
  refine Eq.trans ?_ (congrArg (fun z => restrictSectionAlong (g' ≫ pW) U p' p hp' G
    ((spaceModuleSectionsPullbackCongr (rfl : g' ≫ pW = g' ≫ pW) G).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).map
          (modulePullbackCompIsoHomApp g' pW G)).hom z))) hs₁').symm
  exact restrictSectionAlong_sum_sectionPullback_eq pW k pV hk g' U jV p hjV p' hp' G supp
    σf rV rX hM2 hring'


include hy hWaff hfqc hfqs hG hW hX' in
/-- A section over the fibre that extends to `X ×_Y Spec 𝒪_{Y,y}` extends to the preimage of a
neighbourhood of `y`. -/
theorem exists_open_restrictSectionAlong_eq_of_stalkBaseChange
    (t : spaceModuleSections (representedAlgebraicSpace B S hS U)
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj G))
    (s₀ : spaceModuleSections X' ((modulePullback B S hS (g' ≫ pW)).obj G))
    (hs₀ : restrictSectionAlong (g' ≫ pW) U p' p hp' G s₀ = t) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      ∀ W' : ((BigFppfOver.toScheme B S hS).obj Y).Opens, W' ≤ V → y ∈ W' →
      ∀ ⦃XV : AlgebraicSpaces B S hS⦄ (pV : XV ⟶ X)
        (fV : XV ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y W')),
        IsPullback pV fV f
          (ObjectProperty.homMk (yoneda.map (openSiteObjectHom B S hS Y W'))) →
        ∀ (jV : yoneda.obj U ⟶ XV.1) (h : jV ≫ pV.hom = p),
          ∃ s : spaceModuleSections XV ((modulePullback B S hS pV).obj G),
            restrictSectionAlong pV U jV p h G s = t := by
  have : IsAffine (chartScheme (idEtaleChart B S hS (openSiteObject B S hS Y W))) := hWaff
  have : IsIso (idEtaleChart B S hS (openSiteObject B S hS Y W)).obj.hom :=
    inferInstanceAs (IsIso (𝟙 _))
  have : IsIso (idEtaleChart B S hS (stalkPointObject Y y)).obj.hom :=
    inferInstanceAs (IsIso (𝟙 _))
  have : IsAffine (chartScheme (idEtaleChart B S hS (stalkPointObject Y y))) :=
    isAffine_stalkPointObject Y y
  have hN : ((modulePullback B S hS pW).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS pW G hG
  have hfWqc : IsQuasiCompact B S hS fW.hom :=
    isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS hW) hfqc
  have hfWqs : IsQuasiSeparated B S hS fW.hom :=
    (isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback hW hfqs
  let s₁ := ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).map
        (modulePullbackCompIsoInvApp g' pW G)).hom s₀
  have hspan := mem_span_baseScalars_range_pullbackSection hX' ((modulePullback B S hS pW).obj G)
    (idEtaleChart B S hS (openSiteObject B S hS Y W)) (idEtaleChart B S hS (stalkPointObject Y y))
    (isFlat_stalkPointToOpen Y W hy) hfWqc hfWqs s₁
  let instT : Module (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (representedAlgebraicSpace B S hS (stalkPointObject Y y)).1
      (representedAlgebraicSpace B S hS (stalkPointObject Y y)).2).O).obj)
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).obj
          ((modulePullback B S hS g').obj ((modulePullback B S hS pW).obj G))) :=
    Module.compHom _ (globalSectionsRingHomSite B S hS f')
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hspan
  have hs₁ : s₁ = ∑ σ ∈ c.support,
      globalSectionsRingHomSite B S hS f' (c σ) •
        sectionPullback g' ((modulePullback B S hS pW).obj G) σ := hc.symm
  clear hc hspan
  clear_value instT
  clear instT
  obtain ⟨V, hVW, hyV, a, ha⟩ :=
    exists_le_forall_globalSectionsRingHomSite_stalkPointToOpen_eq Y W hy c.support (fun σ => c σ)
  refine ⟨V, hyV, fun W' hW'V hyW' =>
    exists_restrictSectionAlong_eq_of_coefficients hy f G
      pW fW hW g' f' hX' U p p' hp' t s₀ hs₀ _
      (modulePullbackCompIsoHomApp_modulePullbackCompIsoInvApp_apply g' pW G s₀)
      c.support (fun σ => c σ) hs₁ W' (hW'V.trans hVW) hyW'
      (fun σ => globalSectionsRingHomSite B S hS
        (representedSpaceMap B S hS (openSiteObjectHomOfLE Y hW'V)) (a σ)) fun σ hσ => ?_⟩
  have e1 := RingHom.congr_fun (globalSectionsRingHomSite_comp B S hS
    (representedSpaceMap B S hS (stalkPointToOpen Y W' hyW'))
    (representedSpaceMap B S hS (openSiteObjectHomOfLE Y hW'V))) (a σ)
  have e2 : representedSpaceMap B S hS (stalkPointToOpen Y W' hyW') ≫
      representedSpaceMap B S hS (openSiteObjectHomOfLE Y hW'V) =
        representedSpaceMap B S hS (stalkPointToOpen Y V hyV) := by
    rw [representedSpaceMap_comp B S hS, stalkPointToOpen_comp_openSiteObjectHomOfLE Y V hyV]
  exact e1.symm.trans ((congrArg (fun φ => globalSectionsRingHomSite B S hS φ (a σ)) e2).trans
    (ha σ hσ))

end Lift

end AlgebraicGeometry.Space

end
