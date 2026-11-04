module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingChartTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.OrderedCechHgroup
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealTowerComparisonElements
public import StacksFrontier.Algebra.Homology.DegreeZeroTowerHomology
public import StacksFrontier.RingTheory.Cech.GradedDegreeZeroTower

/-!
# The comparison along the infinitesimal neighbourhoods of a zero scheme, by Čech complexes

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module, `s ∈ Γ(X, L)` with zero scheme `Q` and
infinitesimal neighbourhoods `Qₙ`, and `ℱ` a quasi-coherent `𝒪_X`-module, with section ring
`A = Γ_*(X, L)`, graded module `M = Γ_*(X, L, ℱ)` and `f ∈ A₁` the element given by `s`. Let
`g₁, …, g_r ∈ A` be homogeneous of positive degree, given by sections `αᵢ` whose nonvanishing
opens cover `X`, and suppose the nonvanishing opens of homogeneous elements of positive degree are
affine.

This file proves: **if `M` is Noetherian and a power of `f` annihilates the cohomology of the
Čech complex `C^•(g; M)` in degrees `≤ σ + 1`, then the comparison map
`Hᵖ(X, ℱ) ⟶ lim Hᵖ(Qₙ, ℱₙ)` of [Stacks, Tag 0EL1] is an isomorphism for every `p < σ`.**

## The argument

The covering `{X_{αᵢ}}` has affine finite intersections, so `Hᵖ(X, ℱ)` and `Hᵖ(X, ιₙ_* ℱₙ)` are
the cohomology groups of the ordered Čech complexes of the covering
(`Stacks.Algebraization.hgroupIsoOrderedCechHomology`), naturally in the module. The ordered Čech
complex of `ℱ` is the degree-zero part of `C^{•+1}(g; M)`
(`Stacks.SectionRingChartCech.ordCochainLift`), the restriction to `Q_{N k}` is degreewise
surjective, and its kernel is the set of multiples of `f^{N k}` by elements of degree `-N k`
(`Stacks.SectionRingChartTower.unit_app_eq_zero_iff`), where `N` is a common multiple of the
degrees of the product charts. The degree-zero tower comparison
(`Stacks.DegreeZeroTower.homology_tower_bijective`) then makes the comparison along the cofinal
subtower `(Q_{N k})_k` bijective, and cofinality gives the whole tower.

## Main results

* `Stacks.SectionPowerCechComparison.isIso_zeroSchemeComparison_of_cech`: the statement above.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistModule)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingChartCech
open Stacks.Cohomology.CechSheaf (orderedModuleComplex orderedModuleMap)
open Stacks.CochainHomologyElements

universe u

attribute [local instance] instVAddNatIntGradedLocalizedModule

namespace Stacks.SectionPowerCechComparison

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The intersections of the charts -/

section Inter

variable {r : ℕ} {d : Fin r → ℕ} (α : ∀ i, powSections L (d i))

/-- The set of indices of a tuple. -/
abbrev tupleSet {q : ℕ} (τ : Fin (q + 1) → ULift.{u} (Fin r)) : Finset (Fin r) :=
  Finset.image (fun k => (τ k).down) Finset.univ

/-- The set of indices of a tuple is nonempty. -/
theorem tupleSet_nonempty {q : ℕ} (τ : Fin (q + 1) → ULift.{u} (Fin r)) :
    (tupleSet τ).Nonempty :=
  ⟨(τ 0).down, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

/-- The intersection of the charts along an arbitrary tuple is the nonvanishing open of the
product chart of its set of indices. -/
theorem iInf_chartOpen_eq {q : ℕ} (τ : Fin (q + 1) → ULift.{u} (Fin r)) :
    (⨅ k, chartOpen L α (τ k)) =
      nvOpen L (prodSec L α (tupleSet τ) (tupleSet_nonempty τ)) := by
  rw [nvOpen_prodSec]
  apply le_antisymm
  · refine le_iInf₂ fun i hi => ?_
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hi
    exact (iInf_le _ k).trans (by rw [← hk])
  · exact le_iInf fun k => iInf₂_le (f := fun i (_ : i ∈ tupleSet τ) => nvOpen L (α i)) (τ k).down
      (Finset.mem_image_of_mem _ (Finset.mem_univ k))

/-- If the nonvanishing opens of the sections `α i` cover `X`, then so do the charts. -/
theorem top_eq_iSup_chartOpen (hcov : ⨆ i, nvOpen L (α i) = ⊤) :
    (⊤ : X.Opens) = ⨆ i, chartOpen L α i := by
  rw [← hcov]
  exact le_antisymm (iSup_le fun i => le_iSup_of_le (ULift.up i) le_rfl)
    (iSup_le fun i => le_iSup_of_le i.down le_rfl)

end Inter

/-! ### Functoriality of the ordered Čech complex -/

variable {ι : Type u} [LinearOrder ι] (W : ι → X.Opens) (hW : (⊤ : X.Opens) = ⨆ i, W i)

/-- The map of ordered Čech complexes induced by a composite of morphisms of modules is the
composite of the induced maps. -/
theorem orderedModuleMap_comp {G G' G'' : X.Modules} (φ : G ⟶ G') (φ' : G' ⟶ G'') :
    orderedModuleMap ⊤ W hW (φ ≫ φ') = orderedModuleMap ⊤ W hW φ ≫ orderedModuleMap ⊤ W hW φ' := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  funext k
  show ConcreteCategory.hom ((Stacks.Cohomology.CechSheaf.abSectionsMap (φ ≫ φ')).app _) (y k) =
    ConcreteCategory.hom ((Stacks.Cohomology.CechSheaf.abSectionsMap φ').app _)
      (ConcreteCategory.hom ((Stacks.Cohomology.CechSheaf.abSectionsMap φ).app _) (y k))
  rw [show Stacks.Cohomology.CechSheaf.abSectionsMap (φ ≫ φ') =
      Stacks.Cohomology.CechSheaf.abSectionsMap φ ≫ Stacks.Cohomology.CechSheaf.abSectionsMap φ'
    from (PresheafOfModules.toPresheaf _).map_comp φ.val φ'.val]
  rfl

/-! ### The restriction to an infinitesimal neighbourhood, on the ordered Čech cochains -/

section Restriction

open Stacks.LocalCohomology (ordIndexEquiv cechComponent)
open Stacks.SectionRingChartTower (sectionElt)

/-- Transport of a multiple of a scalar along the identification of the localizations at two
equal elements. -/
theorem exists_localizedEquivOfEq_iff {S : Type*} {N : Type*} {σ' : Type*} {τ : Type*}
    [CommRing S] [AddCommGroup N] [Module S N] [SetLike σ' S] (𝒜 : ℕ → σ') [SetLike τ N]
    (𝒨 : ℤ → τ) {a b : S} (h : a = b) (m : ℤ) (c : S) (z : LocalizedModule (Submonoid.powers a) N) :
    (∃ w ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 a m, z = c • w) ↔
      ∃ w ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 b m, localizedEquivOfEq h z = c • w := by
  subst h
  rfl

variable (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
  {r : ℕ} {d : Fin r → ℕ} (hd : ∀ i, 0 < d i) (α : ∀ i, powSections L (d i))

/-- **A section over a Čech intersection dies on `Q_N`**, for `N` a multiple of the degree of the
product chart, exactly when its lift is `f^N` times an element of degree `-N`. -/
theorem unit_app_inter_eq_zero_iff (s : Γ(L, ⊤)) {p : ℕ}
    (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p)
    (hW : IsAffineOpen (nvOpen L (prodSec L α _ (nonempty_of_card (ordIndexEquiv p σ)))))
    {N k : ℕ} (hN : N = prodDeg L α _ (nonempty_of_card (ordIndexEquiv p σ)) * k)
    (y : Γ(F, CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (zeroScheme X L s ^ N).subschemeι).unit.app
        F).app (CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1) y = 0 ↔
      ∃ w ∈ Stacks.GradedLocalization.gradedPiece (grading L)
          (Stacks.TwistedSections.moduleGrading F L)
          (∏ i ∈ (ordIndexEquiv p σ).1, gen L α i) (-(N : ℕ)),
        tupleLift L hL F hd α σ y = sectionElt L s ^ N • w := by
  subst hN
  have ht := nonempty_of_card (ordIndexEquiv p σ)
  have heq := inter_eq_nvOpen_prodSec L α σ
  let u := (Scheme.Modules.pullbackPushforwardAdjunction
    (zeroScheme X L s ^ (prodDeg L α (ordIndexEquiv p σ).1 ht * k)).subschemeι).unit.app F
  let Q := (Scheme.Modules.pushforward (zeroScheme X L s ^
    (prodDeg L α (ordIndexEquiv p σ).1 ht * k)).subschemeι).obj
      ((Scheme.Modules.pullback (zeroScheme X L s ^
        (prodDeg L α (ordIndexEquiv p σ).1 ht * k)).subschemeι).obj F)
  have hnat : u.app (nvOpen L (prodSec L α (ordIndexEquiv p σ).1 ht))
      (F.presheaf.map (eqToHom heq.symm).op y) = Q.presheaf.map (eqToHom heq.symm).op
        (u.app (CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1) y) := by
    have h := ConcreteCategory.congr_hom (u.mapPresheaf.naturality (eqToHom heq.symm).op) y
    simp only [ConcreteCategory.comp_apply] at h
    exact h
  have hiso : Function.Injective (Q.presheaf.map (eqToHom heq.symm).op) := by
    intro a b hab
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using
      congrArg (Q.presheaf.map (eqToHom heq).op) hab
  have h1 : u.app (CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1) y = 0 ↔
      u.app (nvOpen L (prodSec L α (ordIndexEquiv p σ).1 ht))
        (F.presheaf.map (eqToHom heq.symm).op y) = 0 := by
    rw [hnat]
    exact (map_eq_zero_iff _ hiso).symm
  exact h1.trans <| (Stacks.SectionRingChartTower.unit_app_eq_zero_iff L hL F s
    (prodDeg_pos L hd α (ordIndexEquiv p σ).1 ht) (prodSec L α (ordIndexEquiv p σ).1 ht) hW k
    _).trans <| exists_localizedEquivOfEq_iff (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (of_prodSec L α (ordIndexEquiv p σ).1 ht) _ _ _

end Restriction

/-! ### The restriction on cochains -/

section Cochains

open Stacks.LocalCohomology (ordIndexEquiv cechComponent)
open Stacks.SectionRingChartTower (sectionElt)

variable (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
  {r : ℕ} {d : Fin r → ℕ} (hd : ∀ i, 0 < d i) (α : ∀ i, powSections L (d i))
  (hcov : ⨆ i, nvOpen L (α i) = ⊤)
  (haff : ∀ (e : ℕ) (β : powSections L e), 0 < e → IsAffineOpen (nvOpen L β))

include hd haff in
/-- If the nonvanishing opens of homogeneous sections of positive degree are affine, then so is
the intersection of the charts along an ordered tuple of indices. -/
theorem isAffineOpen_inter {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    IsAffineOpen (CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1) := by
  rw [inter_eq_nvOpen_prodSec L α σ]
  exact haff _ _ (prodDeg_pos L hd α _ _)

/-- The component of a Čech cochain at a set of indices, as a function of a scalar multiple. -/
theorem cechComponent_smul {R : Type*} [CommRing R] {q : ℕ} (g : Fin q → R)
    (M : ModuleCat R) (p : ℕ) (t : {t : Finset (Fin q) // t.card = p}) (a : R)
    (z : Cech.cechTerm g (M : Type _) p) :
    cechComponent g M p t (a • z) = a • cechComponent g M p t z :=
  map_smul _ a z

include haff in
/-- **The kernel of the restriction to `Q_N`, on ordered Čech cochains**, for `N` a multiple of
the degrees of all the product charts: a cochain dies exactly when its lift is `f^N` times a
cochain of degree `-N`. -/
theorem ordCochain_unit_eq_zero_iff (s : Γ(L, ⊤)) {N : ℕ}
    (hN : ∀ (t : Finset (Fin r)) (ht : t.Nonempty), prodDeg L α t ht ∣ N) (p : ℕ)
    (x : CechCochains.OrdCochain (X := TopCat.of X) (chartOpen L α)
      (Stacks.Cohomology.CechSheaf.abSections F) p) :
    (∀ σ, ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L s ^ N).subschemeι).unit.app F).app _ (x σ) = 0) ↔
      ∃ w ∈ Cech.gradedCechTerm (grading L) (Stacks.TwistedSections.moduleGrading F L)
          (gen L α) (-(N : ℕ)) (p + 1),
        ordCochainLift L hL F hd α p x = sectionElt L s ^ N • w := by
  classical
  have hkey : ∀ σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p,
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L s ^ N).subschemeι).unit.app F).app _ (x σ) = 0 ↔
      ∃ w ∈ Stacks.GradedLocalization.gradedPiece (grading L)
          (Stacks.TwistedSections.moduleGrading F L)
          (∏ i ∈ (ordIndexEquiv p σ).1, gen L α i) (-(N : ℕ)),
        tupleLift L hL F hd α σ (x σ) = sectionElt L s ^ N • w := fun σ => by
    obtain ⟨k, hk⟩ := hN _ (nonempty_of_card (ordIndexEquiv p σ))
    exact unit_app_inter_eq_zero_iff L hL F hd α s σ (haff _ _ (prodDeg_pos L hd α _ _)) hk (x σ)
  constructor
  · intro h
    choose w hw hxw using fun σ => (hkey σ).1 (h σ)
    refine ⟨∑ σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p,
      DirectSum.lof (sectionRing L) {t : Finset (Fin r) // t.card = p + 1}
        (fun t => Cech.cechMod (gen L α) (twistModule F L) t.1) (ordIndexEquiv p σ) (w σ),
      AddSubgroup.sum_mem _ fun σ _ => Cech.lof_mem_gradedCechTerm _ (hw σ), ?_⟩
    rw [ordCochainLift_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [hxw σ, map_smul]
  · rintro ⟨w, hw, hxw⟩ σ
    refine (hkey σ).2 ⟨cechComponent (gen L α) (ModuleCat.of (sectionRing L) (twistModule F L))
      (p + 1) (ordIndexEquiv p σ) w, Cech.mem_gradedCechTerm.1 hw _, ?_⟩
    rw [← cechComponent_ordCochainLift L hL F hd α p x σ, hxw, cechComponent_smul]

include hd haff in
/-- **The restriction to `Q_N` is surjective on ordered Čech cochains.** -/
theorem ordCochain_unit_surjective (s : Γ(L, ⊤)) (N p : ℕ)
    (y : CechCochains.OrdCochain (X := TopCat.of X) (chartOpen L α)
      (Stacks.Cohomology.CechSheaf.abSections
        ((Scheme.Modules.pushforward (zeroScheme X L s ^ N).subschemeι).obj
          ((Scheme.Modules.pullback (zeroScheme X L s ^ N).subschemeι).obj F))) p) :
    ∃ x : CechCochains.OrdCochain (X := TopCat.of X) (chartOpen L α)
        (Stacks.Cohomology.CechSheaf.abSections F) p,
      ∀ σ, ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L s ^ N).subschemeι).unit.app F).app _ (x σ) = y σ := by
  choose x hx using fun σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p =>
    Stacks.SectionRingChartTower.unit_app_surjective (zeroScheme X L s) N F
      (isAffineOpen_inter L hd α haff σ) (y σ)
  exact ⟨x, hx⟩

end Cochains

/-! ### Transport of the comparison along the ordered Čech complexes -/

section Transport

open Stacks.Algebraization.IdealTower (system)

variable {X : Scheme.{u}} (J : ℕ → X.IdealSheafData) (hJ : ∀ n, J (n + 1) ≤ J n)
  (F : X.Modules) [F.IsQuasicoherent] [∀ n, ((system J hJ F).obj (op n)).IsQuasicoherent]
  {ι' : Type u} [LinearOrder ι'] (W : ι' → X.Opens) (hW : (⊤ : X.Opens) = ⨆ i, W i)
  (haff : ∀ (r : ℕ) (s : Fin (r + 1) → ι'), IsAffineOpen (⨅ k, W (s k)))

include haff in
/-- **The comparison of a tower of thickenings is an isomorphism as soon as it is so on the
ordered Čech cohomology of an affine covering, along a cofinal subtower `(Q_{N k})_k`.** -/
theorem isIso_comparison_of_orderedCech (p N : ℕ) (hN : 1 ≤ N)
    (hinj : Function.Injective fun x : (orderedModuleComplex ⊤ W hW F).homology p => fun k =>
      HomologicalComplex.homologyMap (orderedModuleMap ⊤ W hW
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Stacks.Algebraization.IdealTower.ι J (N * k))).unit.app F)) p x)
    (hsurj : ∀ y : ∀ k, (orderedModuleComplex ⊤ W hW ((system J hJ F).obj (op (N * k)))).homology p,
      (∀ k, HomologicalComplex.homologyMap (orderedModuleMap ⊤ W hW
        ((system J hJ F).map (homOfLE (Nat.mul_le_mul_left N (Nat.le_succ k))).op)) p
          (y (k + 1)) = y k) →
      ∃ x, ∀ k, HomologicalComplex.homologyMap (orderedModuleMap ⊤ W hW
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Stacks.Algebraization.IdealTower.ι J (N * k))).unit.app F)) p x = y k) :
    IsIso (Stacks.Algebraization.IdealTower.comparison J hJ F p) := by
  let Θ : ∀ (G : X.Modules) [G.IsQuasicoherent], _ := fun G _ =>
    Stacks.Algebraization.hgroupIsoOrderedCechHomology X W hW haff G p
  have hΘ : ∀ {G G' : X.Modules} [G.IsQuasicoherent] [G'.IsQuasicoherent] (φ : G ⟶ G')
      (x : Hgroup X.ringCatSheaf ⊤ p G),
      (Θ G').hom ((Hfunctor X.ringCatSheaf ⊤ p).map φ x) =
        HomologicalComplex.homologyMap (orderedModuleMap ⊤ W hW φ) p ((Θ G).hom x) :=
    fun φ x => ConcreteCategory.congr_hom
      (Stacks.Algebraization.hgroupIsoOrderedCechHomology_naturality X W hW haff φ p) x
  refine Stacks.Algebraization.IdealTower.isIso_comparison_of_elements_mul J hJ F p N hN
    (fun x hx => ?_) (fun t ht => ?_)
  · have h0 : ∀ k, HomologicalComplex.homologyMap (orderedModuleMap ⊤ W hW
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Stacks.Algebraization.IdealTower.ι J (N * k))).unit.app F)) p
          ((Θ F).hom x) = 0 := fun k => by
      refine (hΘ (G' := (system J hJ F).obj (op (N * k))) _ x).symm.trans ?_
      exact (congrArg (Θ ((system J hJ F).obj (op (N * k)))).hom (hx (N * k))).trans (map_zero _)
    exact (ConcreteCategory.bijective_of_isIso (Θ F).hom).1
      ((hinj (funext fun k => (h0 k).trans (map_zero _).symm)).trans (map_zero _).symm)
  · have hcompat : ∀ k, HomologicalComplex.homologyMap (orderedModuleMap ⊤ W hW
        ((system J hJ F).map (homOfLE (Nat.mul_le_mul_left N (Nat.le_succ k))).op)) p
          ((Θ _).hom (t (N * (k + 1)))) = (Θ _).hom (t (N * k)) := fun k =>
      (hΘ _ _).symm.trans (by rw [ht])
    obtain ⟨x', hx'⟩ := hsurj (fun k => (Θ _).hom (t (N * k))) hcompat
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Θ F).hom).2 x'
    refine ⟨x, fun k => ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (Θ ((system J hJ F).obj (op (N * k)))).hom).1
    refine (hΘ (G' := (system J hJ F).obj (op (N * k))) _ x).trans ?_
    rw [hx]
    exact hx' k

end Transport

section Main

open Stacks.LocalCohomology (ordIndexEquiv)
open Stacks.SectionRingChartTower (sectionElt sectionElt_mem)
open Stacks.Algebraization.IdealTower (system cone)

variable (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
  {r : ℕ} {d : Fin r → ℕ} (hd : ∀ i, 0 < d i) (α : ∀ i, powSections L (d i))
  (hcov : ⨆ i, nvOpen L (α i) = ⊤)
  (haff : ∀ (e : ℕ) (β : powSections L e), 0 < e → IsAffineOpen (nvOpen L β))

include hL hd hcov haff in
/-- **The comparison of [Stacks, Tag 0EL1], from an annihilation of the Čech cohomology of
`Γ_*(X, L, ℱ)`.** -/
theorem isIso_zeroSchemeComparison_of_cech (s : Γ(L, ⊤))
    [IsNoetherian (sectionRing L) (twistModule F L)] {c σ : ℕ}
    (hH : ∀ j : ℕ, j ≤ σ + 1 →
      ∀ x : (_root_.Cech.cechComplex (gen L α) (twistModule F L)).homology j,
        sectionElt L s ^ c • x = 0)
    (p : ℕ) (hp : p < σ) :
    IsIso (Stacks.Algebraization.zeroSchemeComparison X L s F p) := by
  classical
  set N := (∑ i, d i).factorial
  have hN1 : 1 ≤ N := Nat.factorial_pos _
  have hNdvd : ∀ (t : Finset (Fin r)) (ht : t.Nonempty), prodDeg L α t ht ∣ N := by
    intro t ht
    refine Nat.dvd_factorial (prodDeg_pos L hd α t ht) ?_
    rw [prodDeg_eq]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ t)
  have hW := top_eq_iSup_chartOpen L α hcov
  have haffT : ∀ (q : ℕ) (τ : Fin (q + 1) → ULift.{u} (Fin r)),
      IsAffineOpen (⨅ k, chartOpen L α (τ k)) := by
    intro q τ
    rw [iInf_chartOpen_eq]
    exact haff _ _ (prodDeg_pos L hd α _ _)
  have hneg : ∀ j : ℤ, j < 0 → ∀ x ∈ Stacks.TwistedSections.moduleGrading F L j, x = 0 := by
    intro j hj x hx
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    exact AddSubgroup.mem_bot.1 hx
  have hc (i) : gen L α i ∈ grading L (d i) := Stacks.ExternalGrading.of_mem_summand (d i) (α i)
  obtain ⟨N₀, hinjA⟩ := Stacks.GradedDegreeZeroTower.mem_bd_of_sub_pow_smul_mem_bd (grading L)
    (Stacks.TwistedSections.moduleGrading F L) (gen L α) hc (sectionElt_mem L s) hneg hH
  obtain ⟨e, hsurjA⟩ := Stacks.GradedDegreeZeroTower.exists_cocycle_sub_eq_pow_smul (grading L)
    (Stacks.TwistedSections.moduleGrading F L) (gen L α) hc (sectionElt_mem L s) hneg hH
  let Jt := Stacks.Algebraization.zeroSchemeTowerIdeal X L s
  let hJ := Stacks.Algebraization.zeroSchemeTowerIdeal_succ_le X L s
  let Q : ℕ → X.Modules := fun n => (system Jt hJ F).obj (op n)
  have hQ : ∀ n, (Q n).IsQuasicoherent := fun n =>
    Stacks.SectionRingChartTower.isQuasicoherent_restriction (zeroScheme X L s) n F
  let unit : ∀ n, F ⟶ Q n := fun n =>
    (Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Algebraization.IdealTower.ι Jt n)).unit.app F
  let trans : ∀ {n m : ℕ}, n ≤ m → (Q m ⟶ Q n) := fun h => (system Jt hJ F).map (homOfLE h).op
  let K := orderedModuleComplex ⊤ (chartOpen L α) hW F
  let Kt : ℕ → _ := fun k => orderedModuleComplex ⊤ (chartOpen L α) hW (Q (N * k))
  let π : ∀ k, K ⟶ Kt k := fun k => orderedModuleMap ⊤ (chartOpen L α) hW (unit (N * k))
  let τ : ∀ k, Kt (k + 1) ⟶ Kt k := fun k =>
    orderedModuleMap ⊤ (chartOpen L α) hW (trans (Nat.mul_le_mul_left N (Nat.le_succ k)))
  have hπτ : ∀ k, π (k + 1) ≫ τ k = π k := fun k => (orderedModuleMap_comp _ hW _ _).symm.trans
    (congrArg (orderedModuleMap ⊤ (chartOpen L α) hW) ((cone Jt hJ F).w _))
  obtain ⟨hinjE, hsurjE⟩ := Stacks.DegreeZeroTower.homology_tower_bijective
    (C := fun p => _root_.Cech.cechTerm (gen L α) (twistModule F L) (p + 1))
    (d := Stacks.GradedDegreeZeroTower.cechDiff (gen L α))
    (D := Stacks.GradedDegreeZeroTower.degreePart (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (gen L α))
    (f := sectionElt L s) (K := K) (Kt := Kt) (π := π) (τ := τ) hπτ
    (fun p m x hx => Stacks.GradedDegreeZeroTower.smul_mem_gradedCechTerm (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (gen L α) hc (sectionElt_mem L s) hx)
    (fun p => ordCochainLift L hL F hd α p) (fun p => ordCochainLift_injective L hL F hd α p)
    (fun p z => (mem_range_ordCochainLift L hL F hd α p z).symm)
    (fun p x => by
      rw [Stacks.Cohomology.CechSheaf.orderedModuleComplex_d ⊤ (chartOpen L α) hW F p]
      exact ordCochainLift_ordD L hL F hd α p x) hN1
    (fun k p y => by
      obtain ⟨x, hx⟩ := ordCochain_unit_surjective L F hd α haff s (N * k) p y
      exact ⟨x, funext hx⟩)
    (fun k p x => by
      rw [← ordCochain_unit_eq_zero_iff L hL F hd α haff s
        (fun t ht => (hNdvd t ht).trans (Dvd.intro k rfl)) p x]
      exact ⟨fun h σ => congrFun h σ, fun h => funext h⟩)
    p ⟨N₀, hinjA p hp.le⟩ ⟨e, hsurjA p hp⟩
  exact isIso_comparison_of_orderedCech Jt hJ F (chartOpen L α) hW haffT p N hN1 hinjE hsurjE

end Main

end Stacks.SectionPowerCechComparison

end
