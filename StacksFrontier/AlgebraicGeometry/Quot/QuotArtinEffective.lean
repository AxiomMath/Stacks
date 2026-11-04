module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinFormalBase
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTowerExistence
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinEpi
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackApproximation

/-!
# Effectivity of formal objects of the Quot functor (Stacks 0CZW, axiom [4])

* `AlgebraicGeometry.Space.exists_pointsMap_truncation_mem`: the closed fibre of a complete local
  base meets every nonempty closed set of points;
* `AlgebraicGeometry.Space.QuotSituation.exists_quotient_of_formal`: compatible quotients over the
  thickenings of a complete local base algebraize (Stacks 08BE, 08K6);
* `AlgebraicGeometry.Space.isEffective_quotOverBase`: **Stacks 0CZW, axiom [4]**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open Deformation.Artin

/-- **The closed fibre of a complete local base meets every nonempty closed set of points.** -/
theorem exists_pointsMap_truncation_mem (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (hA : B.Contains (Spec (.of A.R)))
    (W : Set (points B S hS ((schemeSpaceFunctor B S hS).obj (baseOver B S hS A hA)).1))
    (hW : IsClosed W) (hne : W.Nonempty) :
    ∃ y₀, pointsMap B S hS ((schemeSpaceFunctor B S hS).obj (truncationOver B S hS A contains 0)).1
      ((schemeSpaceFunctor B S hS).map (restrictionToBase B S hS A hA contains 0)).hom y₀ ∈ W := by
  have : IsLocalRing A.R := A.localRing
  let I := maximalIdeal A.R
  have hW' : IsClosed (pointsToScheme B S hS (baseOver B S hS A hA) '' W) :=
    (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS _ W).1 hW
  obtain ⟨w, hw⟩ := hne
  have hcl : (closedPoint A.R : Spec (.of A.R)) ∈
      pointsToScheme B S hS (baseOver B S hS A hA) '' W :=
    (specializes_closedPoint (pointsToScheme B S hS (baseOver B S hS A hA) w)).mem_closed hW'
      ⟨w, hw, rfl⟩
  have : Nontrivial (A.R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [zero_add, pow_one]
    exact (maximalIdeal.isMaximal A.R).ne_top)
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum (A.R ⧸ I ^ (0 + 1))) := inferInstance
  obtain ⟨y₀, hy₀⟩ := surjective_pointsToScheme B S hS (truncationOver B S hS A contains 0)
    (show (BigFppfOver.toScheme B S hS).obj (truncationOver B S hS A contains 0) from q)
  refine ⟨y₀, ?_⟩
  obtain ⟨w', hw'W, hw'⟩ := hcl
  have himg : pointsToScheme B S hS (baseOver B S hS A hA)
      (pointsMap B S hS (yoneda.obj (truncationOver B S hS A contains 0))
        (yoneda.map (restrictionToBase B S hS A hA contains 0)) y₀) =
      (closedPoint A.R : Spec (.of A.R)) := by
    rw [pointsToScheme_pointsMap_yoneda, restrictionToBase_toScheme, hy₀]
    show PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1))) q = closedPoint A.R
    ext1
    refine le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.comap _ q).isPrime.ne_top) ?_
    intro x hx
    show Ideal.Quotient.mk (I ^ (0 + 1)) x ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by rwa [zero_add, pow_one])]
    exact q.asIdeal.zero_mem
  have := injective_pointsToScheme B S hS (baseOver B S hS A hA) (himg.trans hw'.symm)
  show pointsMap B S hS (yoneda.obj (truncationOver B S hS A contains 0))
    (yoneda.map (restrictionToBase B S hS A hA contains 0)) y₀ ∈ W
  rwa [this]

namespace QuotSituation

variable (D : QuotSituation B S hS) (ι : ∀ T : BigFppfOver B S hS,
    (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]

include ι in
/-- **Compatible quotients over the thickenings of a complete local base algebraize.** For `f`
separated and `F` of finite presentation, a compatible family of quotients of `F` over the
infinitesimal thickenings `Spec A / 𝔪ⁿ⁺¹` of a Noetherian complete local base is the family of
pullbacks of one quotient over `Spec A`: Grothendieck's existence theorem (Stacks 08BE) for the
quotient modules, the representability of `Hom` sheaves (Stacks 08K6) for the quotient map, and
surjectivity of that map on the closed fibre, which meets every closed set. -/
theorem exists_quotient_of_formal (hsep : IsSeparated B S hS D.f.hom)
    (hF : D.F.IsFinitePresentationOnSite)
    (A : FormalBase S) (contains : ∀ n, B.Contains (A.truncation n))
    (hA : B.Contains (Spec (.of A.R)))
    (K : ∀ n, D.properlySupportedQuotients (D.testOver ι (truncationOver B S hS A contains n)))
    (hK : ∀ n, D.quotientPullback (D.testHom ι (truncationOverSucc B S hS A contains n))
      (K (n + 1)).1 = (K n).1) :
    ∃ Kl : D.properlySupportedQuotients (D.testOver ι (baseOver B S hS A hA)),
      ∀ n, D.quotientPullback (D.testHom ι (restrictionToBase B S hS A hA contains n)) Kl.1 =
        (K n).1 := by
  let T := truncationDiagram B S hS A contains
  let c := truncationCocone B S hS A hA contains
  have hT : ∀ n, T.map (homOfLE (n.le_add_right 1)) = truncationOverSucc B S hS A contains n :=
    fun n => Functor.ofSequence_map_homOfLE_succ _ n
  have hK' : ∀ n, D.quotientPullback (D.testHom ι (T.map (homOfLE (n.le_add_right 1))))
      (K (n + 1)).1 = (K n).1 := fun n => by rw [hT]; exact hK n
  let D' := D.toCoherentSituation
  let : Category.{u + 1} (CoherentObject D') := D'.categoryData.category
  let L : ℕ → CoherentObject D' := fun n => D.cohObject _ (K n).1 (K n).2
  let t : ∀ n, CoherentHom (L n) (L (n + 1)) := fun n => D.towerCoherentStep ι (T := T) K hK' n
  let a : ∀ n, (L n).T ⟶ D.testOver ι c.pt := fun n => D.legHom ι c n
  have hta : ∀ n, (t n).base ≫ a (n + 1) = a n := fun n => by
    show D.testHom ι _ ≫ D.testHom ι _ = D.testHom ι _
    rw [← testHom_comp, c.w]
  obtain ⟨x, hx, r, hr, hrb⟩ := D'.exists_realization A contains hA L (fun _ => rfl) t
    (D.testOver ι c.pt) rfl a (fun n => (Category.comp_id _).trans (Category.id_comp _).symm)
    hta hsep
  obtain ⟨T', G, hq, hfp, hfl, hps⟩ := x
  change T' = D.testOver ι c.pt at hx
  subst hx
  have hψ' : ∀ n, ∃ ψ : (modulePullback B S hS (D'.relativeMap (D.legHom ι c n))).obj G ≅
      D.quotientModule _ (K n).1, r n = ⟨D.legHom ι c n, ψ.hom, Iso.isIso_hom _⟩ := by
    intro n
    have hb : (r n).base = D.legHom ι c n := (hrb n).trans (Category.comp_id _)
    generalize r n = rn at hb ⊢
    obtain ⟨b, φ, hφ⟩ := rn
    change b = D.legHom ι c n at hb
    subst hb
    exact ⟨@asIso _ _ _ _ φ hφ, rfl⟩
  choose ψ hψr using hψ'
  obtain ⟨hp, hcl, hpr⟩ := hps
  have hψ : ∀ n, (D.towerCoherentStep ι (T := T) K hK' n).comp
      (⟨D.legHom ι c (n + 1), (ψ (n + 1)).hom, Iso.isIso_hom _⟩ :
        CoherentHom (D.cohObject _ (K (n + 1)).1 (K (n + 1)).2)
          (D.toCoherentSituation.objectOf _ G hq hfp hfl
            ⟨D.isLocallyOfFiniteType_projection _, hcl, hpr⟩)) =
      ⟨D.legHom ι c n, (ψ n).hom, Iso.isIso_hom _⟩ := fun n => by
    have h := hr n
    rw [hψr n, hψr (n + 1)] at h
    exact h
  have hqF : (D.baseChangeModule (D.testOver ι c.pt)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F D.quasicoherent
  have := hfp
  have hGft : SheafOfModules.IsFiniteTypeOnSite G := inferInstance
  have sq : IsPullback (D.relativeMap (D.legHom ι c 0)).hom
      (D.projection (D.testOver ι (T.obj 0))).hom (D.projection (D.testOver ι c.pt)).hom
      ((schemeSpaceFunctor B S hS).map (c.ι.app 0)).hom :=
    AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f (D.legHom ι c 0))
  have hepi0 : ∀ u : D.baseChangeModule (D.testOver ι c.pt) ⟶ G,
      Epi ((modulePullback B S hS (D.relativeMap (D.legHom ι c 0))).map u) → Epi u :=
    fun u hu => by
      refine epi_of_epi_modulePullback_of_hasProperSupport (D.projection (D.testOver ι c.pt))
        (D.isLocallyOfFiniteType_projection _) ((schemeSpaceFunctor B S hS).map (c.ι.app 0))
        (D.projection (D.testOver ι (T.obj 0))) (D.relativeMap (D.legHom ι c 0)) sq
        (exists_pointsMap_truncation_mem A contains hA) hqF hq hGft ⟨hcl, hpr⟩ u ?_
      convert hu using 2
  exact D.exists_quotient_of_tower_of_algebraization_of_epi ι A.isLimitRingCone c
    (truncationIso_spec B S hS A contains) (truncationLimitIso_spec B S hS A hA contains) hF K hK'
    G hq hfp hfl ⟨hcl, hpr⟩ hepi0 ψ hψ

end QuotSituation

section OverBase

variable (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
  (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
  (hF : F.IsQuasicoherentOnSite)

/-- **Stacks 0CZW, axiom [4]: formal objects of `Quot_{F/X/S}` are effective.** For `f`
separated and `F` of finite presentation, every formal object of `𝒮_{Quot_{F/X/S}}` over a
Noetherian complete local ring is effective. This is Grothendieck's existence theorem (Stacks
08BE) applied to the quotient modules, together with the algebraization of the quotient maps
(representability of `Hom` sheaves, Stacks 08K6) and their surjectivity, checked on the closed
fibre. -/
@[stacks 0CZW "axiom [4]: formal objects of Quot_{F/X/S} are effective"]
theorem isEffective_quotOverBase (hsep : IsSeparated B S hS f.hom)
    (hFfp : F.IsFinitePresentationOnSite)
    (ξ : FormalObject B S hS
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.p) :
    FormalObject.IsEffective B S hS
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.p
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).property ξ := by
  let D := quotOverBase X f hf F hF
  let ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y :=
    fun T => ObjectProperty.homMk (yoneda.map (Over.homMk T.hom (by simp)))
  exact isEffective_fibredCategory_of_exists_eq (fun A contains t ht =>
    D.quotSitePresheafModel.formalEffective_of_quotients ι A contains
      (A.contains_spec_of_contains_truncation contains)
      (fun K hK => D.exists_quotient_of_formal ι hsep hFfp A contains _ K hK) t ht) ξ

end OverBase

end AlgebraicGeometry.Space
