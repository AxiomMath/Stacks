module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Topology
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime
import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit

/-!
# Elementary properties of the depth–distance inequalities

Fix an algebraization situation and let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. Uniform
ideal-power torsion makes the `(a, b)`-inequalities automatic, and raising the first bound by
one turns them into the strict inequalities. If moreover `cd(A, I) ≤ d` and `A` has a dualizing
complex, then the `(s, s + d)`-inequalities say exactly that at every point of `U ∩ Y` the
completed local data form a bootstrap situation with bounds `s - δ^Y_Z(y)` and `d`, and the
strict `(s, s + d)`-inequalities imply the ordinary ones.

## Main results

* `Stacks.Algebraization.satisfiesDepthInequalities_of_annihilated` — part (1).
* `Stacks.Algebraization.satisfiesStrictDepthInequalities_of_succ` — part (2).
* `Stacks.Algebraization.satisfiesDepthInequalities_iff_bootstrapSituation` — part (3).
* `Stacks.Algebraization.satisfiesDepthInequalities_of_strict` — part (4).

## Implementation notes

In part (3) a tuple "as in the bootstrap situation" is an element of
`Stacks.Algebraization.BootstrapSituation` whose ring, ideal, module, locus and two integer
bounds are the given data; the ring and module carry algebraic structures, so the
identifications of those are stated with `HEq`. The subtraction `s - δ^Y_Z(y)` needs a finite
distance, so the right-hand side quantifies over the points of `U ∩ Y` at which `δ^Y_Z` is
finite; at a point where it is infinite both inequalities of part (1) hold for free, which is
what makes the equivalence an equivalence and not a restriction. A point of `U ∩ Y` is a point
of `U` together with a point of `Y` with the same image in `X`, as in Stacks 0EJ3.

The finiteness of the formal stalk over the completed local ring, which a bootstrap situation
needs because it carries a finite module, is the second half of Stacks 0EJE and is supplied by
`Stacks.Algebraization.finite_completedStalk_of_isNoetherian`; part (3) therefore carries no
hypothesis of its own beyond those of the source.

Part (4) carries the dualizing-complex hypothesis of the source on `A` even though the proof
given here reaches `dim(𝒪_{X,y}^∧/𝔭) ≤ d` from Stacks 0DXF and so does not consume it; the
binder is therefore named `_hdual`.

`HasDerivedCategory.standard` is pinned as a high-priority local instance, since the derived
category of a dualizing complex is only well defined relative to a model and several are in
scope here.

## References

* [Stacks Project, Tag 0EJ4](https://stacks.math.columbia.edu/tag/0EJ4)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU), the bootstrap
  situation.
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE), the formal stalk.
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open Stacks.AdicCompletionDimension

-- The standard model is pinned at a high priority: `HasDerivedCategory` carries data, so
-- `DerivedCategory C` at two different instances is two different types, and the import
-- closure of this file offers several. Without the priority, the two searches in the
-- statement of `isDualizingComplex_of_ringEquiv_aux` need not pick the same model.
attribute [local instance 10000] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-! ### Stalks of ideal sheaves and of the module systems -/

/-- The sections of the zero subsheaf of a sheaf of modules on a scheme vanish. -/
private theorem submodule_bot_obj
    {X : Scheme.{u}} (G : X.Modules) (U : X.Opens) :
    (⊥ : G.Submodule).obj (op U) = ⊥ := by
  let B : G.Submodule := {
    toSubmodule := ⊥
    isSheaf := by
      intro V s hs
      apply G.isSheaf.section_ext
      rw [Opens.mem_grothendieckTopology] at hs
      intro z hz
      obtain ⟨W, g, hg, hzw⟩ := hs z hz
      refine ⟨W, leOfHom g, hzw, ?_⟩
      let : Module (X.ringCatSheaf.obj.obj (op W)) Γ(G, W) :=
        (G.val.obj (op W)).isModule
      have hgEq : g = homOfLE (leOfHom g) := Subsingleton.elim _ _
      have hg' : (G.presheaf.map g.op).hom s ∈
          (⊥ : G.val.Submodule).obj (op W) := hg
      have hz0 : (G.presheaf.map g.op).hom s = 0 :=
        (Submodule.mem_bot (X.ringCatSheaf.obj.obj (op W))).mp hg'
      rw [← hgEq, hz0]
      exact ((G.presheaf.map g.op).hom.map_zero).symm }
  apply le_antisymm
  · exact (SheafOfModules.Submodule.le_iff.mp (bot_le : (⊥ : G.Submodule) ≤ B)) (op U)
  · exact bot_le

/-- A germ of an ideal sheaf whose `c`-th ideal power annihilates every term of a module system
annihilates the stalk of that term. -/
private theorem idealPowerMultiple_stalk_smul_pow_eq_zero
    {X : Scheme.{u}} (I : X.IdealSheafData) (G : X.Modules) (c : ℕ)
    (hG : _root_.Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I c G = ⊥) (x : X)
    {r : X.presheaf.stalk x}
    (hr : r ∈ IdealSheafData.stalk I x)
    (m : (stalkModuleFunctor x).obj G) : r ^ c • m = 0 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let Ua : X.affineOpens := ⟨U, hU⟩
  have hxU' : x ∈ (Ua : X.Opens) := hxU
  rw [IdealSheafData.stalk_eq_map_germ I x Ua hxU'] at hr
  let : Algebra Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x) :=
    (X.presheaf.germ (Ua : X.Opens) x hxU').hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x)
      (Ua.2.primeIdealOf ⟨x, hxU'⟩).asIdeal :=
    Ua.2.isLocalization_stalk ⟨x, hxU'⟩
  have hr' : r ∈ (I.ideal Ua).map
      (algebraMap Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x)) := by
    simpa only [RingHom.algebraMap_toAlgebra] using hr
  obtain ⟨⟨⟨rU, hrU⟩, t⟩, hrt⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (S := X.presheaf.stalk x)
      (Ua.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl).mp hr'
  obtain ⟨W, hxW, s, hs⟩ := G.presheaf.exists_germ_eq m
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, hW₀W⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  let W₀a : X.affineOpens := ⟨W₀, hW₀⟩
  obtain ⟨f, g, hfg, hxV⟩ :=
    exists_basicOpen_le_affine_inter Ua.2 W₀a.2 x ⟨hxU', hxW₀⟩
  let V := X.affineBasicOpen f
  have hVU : (V : X.Opens) ≤ Ua := X.basicOpen_le f
  have hVW₀ : (V : X.Opens) ≤ W₀a := hfg.trans_le (X.basicOpen_le g)
  have hxV' : x ∈ (V : X.Opens) := hxV
  let rV := (X.presheaf.map (homOfLE hVU).op).hom rU
  let sW₀ := (G.presheaf.map (homOfLE hW₀W).op).hom s
  let sV := (G.presheaf.map (homOfLE hVW₀).op).hom sW₀
  have hrV : rV ∈ I.ideal V := by
    change (X.presheaf.map (homOfLE hVU).op).hom rU ∈ I.ideal V
    rw [← I.map_ideal hVU]
    exact Ideal.mem_map_of_mem _ hrU
  have hlocal :=
    (_root_.Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_le_iff I c G ⊥).mp
      (by rw [hG]) V
  have hkill : rV ^ c • sV = 0 := by
    have hmem := hlocal
      (Submodule.smul_mem_smul (Ideal.pow_mem_pow hrV c)
        (show sV ∈ (⊤ : Submodule _ _) from Submodule.mem_top))
    rw [submodule_bot_obj G V] at hmem
    exact (Submodule.mem_bot Γ(X, (V : X.Opens))).mp hmem
  have hrG : (X.presheaf.germ (V : X.Opens) x hxV').hom rV =
      algebraMap Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x) rU := by
    calc
      (X.presheaf.germ (V : X.Opens) x hxV').hom rV =
          (X.presheaf.germ (Ua : X.Opens) x hxU').hom rU := by
            dsimp [rV]
            exact X.presheaf.germ_res_apply (homOfLE hVU) x hxV' rU
      _ = algebraMap Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x) rU := rfl
  have hsW₀ : G.presheaf.germ (W₀a : X.Opens) x hxW₀ sW₀ = m := by
    dsimp [sW₀]
    exact (TopCat.Presheaf.germ_res_apply G.presheaf
      (homOfLE hW₀W) x hxW₀ s).trans hs
  have hsV : G.presheaf.germ (V : X.Opens) x hxV' sV = m := by
    dsimp [sV]
    exact (TopCat.Presheaf.germ_res_apply G.presheaf
      (homOfLE hVW₀) x hxV' sW₀).trans hsW₀
  let mV : (stalkModuleFunctor x).obj G :=
    G.presheaf.germ (V : X.Opens) x hxV' sV
  have hmV : mV = m := hsV
  have hsmul :
      (X.presheaf.germ (V : X.Opens) x hxV').hom rV ^ c • mV =
        (G.presheaf.germ (V : X.Opens) x hxV' (rV ^ c • sV) :
          (stalkModuleFunctor x).obj G) := by
    let : Module (TopCat.Presheaf.stalk (C := RingCat.{u})
        (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
        (G.presheaf.stalk x) := by
      change Module (TopCat.Presheaf.stalk (C := RingCat.{u})
        X.ringCatSheaf.obj x)
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj G)
      exact ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj G).isModule
    change (SemilinearStalk.commStalkIso X.presheaf x).inv.hom
      ((X.presheaf.germ (V : X.Opens) x hxV').hom rV ^ c) •
      G.presheaf.germ (V : X.Opens) x hxV' sV = _
    have hsc : (SemilinearStalk.commStalkIso X.presheaf x).inv.hom
        ((X.presheaf.germ (V : X.Opens) x hxV').hom rV ^ c) =
        (TopCat.Presheaf.germ (C := RingCat.{u})
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)
          (V : X.Opens) x hxV').hom (rV ^ c) := by
      rw [← map_pow]
      change (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm
        ((X.presheaf.germ (V : X.Opens) x hxV').hom (rV ^ c)) = _
      rw [← SemilinearStalk.commStalkRingEquiv_germ]
      exact Equiv.symm_apply_apply _ _
    rw [hsc]
    exact (PresheafOfModules.germ_ringCat_smul (M := G.val) (x := x)
      V hxV' (rV ^ c) sV).symm
  have hkillG :
      (algebraMap Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x) rU) ^ c • m = 0 := by
    calc
      _ = (X.presheaf.germ (V : X.Opens) x hxV').hom rV ^ c •
          mV := by rw [hrG, hmV]
      _ = 0 := by
        rw [hsmul, hkill]
        exact (G.presheaf.germ (V : X.Opens) x hxV').hom.map_zero
  have hu : IsUnit (algebraMap Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x) t) :=
    IsLocalization.map_units _ t
  apply (hu.pow c).smul_eq_zero.mp
  calc
    (algebraMap Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x) t) ^ c • (r ^ c • m) =
        (r * algebraMap Γ(X, (Ua : X.Opens)) (X.presheaf.stalk x) t) ^ c • m := by
      rw [mul_pow, mul_smul, smul_comm]
    _ = 0 := by rw [hrt]; exact hkillG

/-- The stalk at a point of `U` of the ideal sheaf `I𝒪_U` is the image of `I` under the
composite `A → 𝒪_{X,x} → 𝒪_{U,y}`. -/
private theorem stalkIdeal_eq_map_base
    (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) :
    let x := S.U.ι.base y
    let f : S.A →+* S.U.toScheme.presheaf.stalk y :=
      ((S.U.ι.stalkMap y).hom.comp
        (((S.X.presheaf.germ ⊤ x (Set.mem_univ x)).hom).comp
          (Scheme.ΓSpecIso (.of S.A)).inv.hom))
    IdealSheafData.stalk (idealOnOpen S) y = S.I.map f := by
  classical
  dsimp only
  let x := S.U.ι.base y
  let T : S.X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop
    (S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom)
  have hstalk := IdealSheafData.stalk_comap T S.U.ι y
  have hT : T.ideal ⟨⊤, isAffineOpen_top S.X⟩ =
      S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom := by
    simp [T, Scheme.IdealSheafData.ofIdealTop]
  change IdealSheafData.stalk (T.comap S.U.ι) y = _
  rw [hstalk, IdealSheafData.stalk_eq_map_germ T x
    ⟨⊤, isAffineOpen_top S.X⟩ (Set.mem_univ x), hT, Ideal.map_map, Ideal.map_map]
  congr 1

/-- The cohomological dimension of `I𝒪_{X,y}^∧` in the completed local ring is at most that of
`I` in `A`. -/
private theorem completedLocal_cohomologicalDimension_le
    (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme)
    (d : ℤ)
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) ≤ d) :
    _root_.Stacks.LocalCohomology.cohomologicalDimension
        (completedLocalRing (idealOnOpen S) y)
        (completedLocalIdeal (idealOnOpen S) y)
        (IsNoetherian.noetherian
          (completedLocalIdeal (idealOnOpen S) y)) ≤ d := by
  classical
  let x := S.U.ι.base y
  let R₀ := S.U.toScheme.presheaf.stalk y
  let J₀ := IdealSheafData.stalk (idealOnOpen S) y
  let R := completedLocalRing (idealOnOpen S) y
  let J := completedLocalIdeal (idealOnOpen S) y
  let f : S.A →+* R₀ :=
    ((S.U.ι.stalkMap y).hom.comp
      (((S.X.presheaf.germ ⊤ x (Set.mem_univ x)).hom).comp
        (Scheme.ΓSpecIso (.of S.A)).inv.hom))
  let g : R₀ →+* R := algebraMap R₀ R
  have hJ₀ : J₀ = Ideal.map f S.I := stalkIdeal_eq_map_base S y
  have hcd₀ : _root_.Stacks.LocalCohomology.cohomologicalDimension R₀ J₀
      (IsNoetherian.noetherian J₀) ≤ d := by
    rw [hJ₀]
    exact (_root_.Stacks.LocalCohomology.cohomologicalDimension_map_le f S.I
      (IsNoetherian.noetherian S.I)).trans hcd
  change _root_.Stacks.LocalCohomology.cohomologicalDimension R J
    (IsNoetherian.noetherian J) ≤ d
  exact (_root_.Stacks.LocalCohomology.cohomologicalDimension_map_le g J₀
    (IsNoetherian.noetherian J₀)).trans hcd₀

/-- At a point of `U ∩ Y` the stalk of `I𝒪_U` lies in the maximal ideal of the local ring. -/
private theorem stalkIdeal_le_maximal
    (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) :
    IdealSheafData.stalk (idealOnOpen S) y ≤
      IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk y) := by
  classical
  let x := S.U.ι.base y
  let x₀ : PrimeSpectrum S.A := x
  let g : Γ(S.X, ⊤) →+* S.X.presheaf.stalk x :=
    (S.X.presheaf.germ ⊤ x (Set.mem_univ x)).hom
  let f0 : S.A →+* S.X.presheaf.stalk x :=
    g.comp (Scheme.ΓSpecIso (.of S.A)).inv.hom
  let f1 : S.X.presheaf.stalk x →+* S.U.toScheme.presheaf.stalk y :=
    (S.U.ι.stalkMap y).hom
  have hIpx : S.I ≤ x₀.asIdeal := by
    have hx₀ : x₀ = S.Yι.base z := by
      change (S.U.ι.base y : PrimeSpectrum S.A) = _
      exact congrArg (fun t : S.X => (t : PrimeSpectrum S.A)) hyz
    rw [hx₀]
    let z₀ : PrimeSpectrum (S.A ⧸ S.I) := z
    change S.I ≤ z₀.asIdeal.comap (Ideal.Quotient.mk S.I)
    intro a ha
    change Ideal.Quotient.mk S.I a ∈ z₀.asIdeal
    have hz : Ideal.Quotient.mk S.I a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hz]
    exact z₀.asIdeal.zero_mem
  have hmaxX : Ideal.map f0 x₀.asIdeal =
      maximalIdeal (S.X.presheaf.stalk x) := by
    have htoStalk : f0 = (StructureSheaf.toStalk S.A x₀).hom := by
      dsimp [f0, g, StructureSheaf.toStalk]
      rw [Scheme.ΓSpecIso_inv]
      rfl
    have : IsLocalRing ((structurePresheafInCommRingCat S.A).stalk x₀) := by
      change IsLocalRing (S.X.presheaf.stalk x)
      infer_instance
    have hmax := IsLocalization.AtPrime.map_eq_maximalIdeal x₀.asIdeal
      ((structurePresheafInCommRingCat S.A).stalk x₀)
    have hmapEq : algebraMap S.A
        ((structurePresheafInCommRingCat S.A).stalk x₀) =
        (StructureSheaf.toStalk S.A x₀).hom := by
      ext a
      exact StructureSheaf.stalkAlgebra_map S.A x₀ a
    have hmaxBase : Ideal.map (StructureSheaf.toStalk S.A x₀).hom x₀.asIdeal =
        maximalIdeal ((structurePresheafInCommRingCat S.A).stalk x₀) := by
      simpa [hmapEq] using hmax
    rw [htoStalk]
    convert hmaxBase using 1 <;> rfl
  have hmapX :
      Ideal.map f0 S.I ≤ maximalIdeal (S.X.presheaf.stalk x) :=
    (Ideal.map_mono hIpx).trans hmaxX.le
  have hf1 : Function.Surjective f1 :=
    (ConcreteCategory.bijective_of_isIso (S.U.ι.stalkMap y)).2
  have hmap :
      Ideal.map f1 (maximalIdeal (S.X.presheaf.stalk x)) =
        maximalIdeal (S.U.toScheme.presheaf.stalk y) :=
    IsLocalRing.map_maximalIdeal_of_surjective f1 hf1
  have hstalk := stalkIdeal_eq_map_base S y
  rw [hstalk, ← Ideal.map_map]
  change Ideal.map f1 (Ideal.map f0 S.I) ≤ _
  calc
    Ideal.map f1 (Ideal.map f0 S.I) ≤
        Ideal.map f1 (maximalIdeal (S.X.presheaf.stalk x)) := Ideal.map_mono hmapX
    _ = maximalIdeal (S.U.toScheme.presheaf.stalk y) := hmap

/-! ### Completions of Noetherian local rings -/

/-! ### Depth under localization and completion -/

/-- Localizing a module at a prime of a localization computes the same depth as localizing it
directly at the contracted prime. -/
private theorem depth_localizedModule_localizationAtPrime
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (q : Ideal A) [q.IsPrime] (r : Ideal (Localization.AtPrime q)) [r.IsPrime] :
    Module.depth (Localization.AtPrime (r.comap (algebraMap A (Localization.AtPrime q))))
        (maximalIdeal (Localization.AtPrime (r.comap (algebraMap A (Localization.AtPrime q)))))
        (LocalizedModule (r.comap (algebraMap A (Localization.AtPrime q))).primeCompl M) =
      Module.depth (Localization.AtPrime r) (maximalIdeal (Localization.AtPrime r))
        (LocalizedModule r.primeCompl (LocalizedModule q.primeCompl M)) := by
  classical
  let p := r.comap (algebraMap A (Localization.AtPrime q))
  let L0 := Localization.AtPrime p
  let L1 := Localization.AtPrime r
  let M0 := LocalizedModule p.primeCompl M
  let Mq := LocalizedModule q.primeCompl M
  let M1 := LocalizedModule r.primeCompl Mq
  let e : L0 ≃ₐ[A] L1 :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization q.primeCompl r
  let : Algebra L0 L1 := RingHom.toAlgebra e.toRingEquiv.toRingHom
  let : Module L1 M0 := Module.compHom M0 e.toRingEquiv.symm.toRingHom
  let : IsScalarTower L0 L1 M0 := IsScalarTower.of_algebraMap_smul fun x m => by
    have hx : e.toRingEquiv.symm (algebraMap L0 L1 x) = x := by
      have hmap : algebraMap L0 L1 = e.toRingEquiv.toRingHom := rfl
      rw [hmap]
      exact e.toRingEquiv.symm_apply_apply x
    exact congrArg (fun z => z • m) hx
  let : IsScalarTower A L0 L1 := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (e.commutes x).symm)
  let : IsScalarTower A L1 M0 := IsScalarTower.of_algebraMap_smul fun x m => by
    change e.toRingEquiv.symm (algebraMap A L1 x) • m = x • m
    have hcomm : e.toRingEquiv (algebraMap A L0 x) = algebraMap A L1 x := e.commutes x
    calc
      e.toRingEquiv.symm (algebraMap A L1 x) • m = (algebraMap A L0 x) • m := by
        rw [← hcomm, e.toRingEquiv.symm_apply_apply]
      _ = x • m := IsScalarTower.algebraMap_smul L0 x m
  let f₁ : M →ₗ[A] Mq := LocalizedModule.mkLinearMap q.primeCompl M
  let f₂ : Mq →ₗ[Localization.AtPrime q] M1 := LocalizedModule.mkLinearMap r.primeCompl Mq
  let f : M →ₗ[A] M1 := (f₂.restrictScalars A).comp f₁
  have hstandard : IsBaseChange L1 (LocalizedModule.mkLinearMap p.primeCompl M) :=
    IsLocalizedModule.isBaseChange p.primeCompl L1 _
  have hfirst : IsBaseChange (Localization.AtPrime q) f₁ :=
    LocalizedModule.isBaseChange q.primeCompl M
  have hsecond : IsBaseChange L1 f₂ := IsLocalizedModule.isBaseChange r.primeCompl L1 f₂
  have hcomp : IsBaseChange L1 f := by
    dsimp [f]
    exact hfirst.comp hsecond
  let eM : M0 ≃ₗ[L1] M1 := hstandard.equiv.symm.trans hcomp.equiv
  have hdepthRing : Module.depth L0 (maximalIdeal L0) M0 =
      Module.depth L1 (maximalIdeal L1) M0 := by
    rw [Module.depth_eq_depth_map_algebraMap e.surjective]
    change Module.depth L1 ((maximalIdeal L0).map e.toRingEquiv.toRingHom) M0 = _
    have hmax : (maximalIdeal L0).map e.toRingEquiv.toRingHom = maximalIdeal L1 :=
      IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
    rw [hmax]
  change Module.depth L0 (maximalIdeal L0) M0 =
    Module.depth L1 (maximalIdeal L1) M1
  exact hdepthRing.trans (Module.depth_eq_depth_of_linearEquiv _ eM)

/-- Equal primes give equal depths of the corresponding localizations. -/
private theorem depth_localizedModule_congr_aux
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (h : p = q) :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) =
      Module.depth (Localization.AtPrime q) (maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl M) := by
  subst q
  rfl

/-- A nonzero module annihilated by the ideal has depth zero. -/
private theorem depth_eq_zero_of_smul_eq_zero_aux
    {A : Type*} [CommRing A] (I : Ideal A)
    {M : Type*} [AddCommGroup M] [Module A M] [Nontrivial M]
    (h : ∀ r ∈ I, ∀ m : M, r • m = 0) : Module.depth A I M = 0 := by
  have hbot : I • (⊤ : Submodule A M) = ⊥ := by
    apply le_antisymm _ bot_le
    refine Submodule.smul_le.mpr ?_
    intro r hr m _
    simpa only [Submodule.mem_bot] using h r hr m
  rw [Module.depth, hbot, ite_eq_right bot_ne_top]
  apply le_antisymm _ bot_le
  refine iSup₂_le fun rs hrs => ?_
  cases rs with
  | nil => simp
  | cons r rs =>
    have hreg := (RingTheory.Sequence.isRegular_cons_iff M r rs).mp hrs.2 |>.1
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    exact (hm (hreg ((h r (hrs.1 r List.mem_cons_self) m).trans (smul_zero r).symm))).elim

/-- For an adically complete ring the depth of the completed module at a prime agrees with the
depth of the module at the contracted prime. -/
private theorem depth_localized_adicCompletion_eq_of_complete
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p' : Ideal (AdicCompletion I A)) [p'.IsPrime] :
    Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl (AdicCompletion I M)) =
      Module.depth
        (Localization.AtPrime (p'.comap (algebraMap A (AdicCompletion I A))))
        (maximalIdeal
          (Localization.AtPrime (p'.comap (algebraMap A (AdicCompletion I A)))))
        (LocalizedModule (p'.comap (algebraMap A (AdicCompletion I A))).primeCompl M) := by
  let p := p'.comap (algebraMap A (AdicCompletion I A))
  let L := Localization.AtPrime p'
  have : p'.LiesOver p := ⟨rfl⟩
  have hpmap : p.map (algebraMap A (AdicCompletion I A)) = p' :=
    Ideal.map_comap_of_surjective _ (AdicCompletion.ofAlgEquiv I).surjective _
  have hfiber : p.map (algebraMap A L) = maximalIdeal L := by
    rw [IsScalarTower.algebraMap_eq A (AdicCompletion I A) L, ← Ideal.map_map,
      hpmap, IsLocalization.AtPrime.map_eq_maximalIdeal]
  rw [AlgebraicGeometry.depth_localized_adicCompletion I p p', hfiber]
  have hzero : Module.depth L (maximalIdeal L) (L ⧸ maximalIdeal L) = 0 := by
    apply depth_eq_zero_of_smul_eq_zero_aux
    intro r hr m
    change (Ideal.Quotient.mk (maximalIdeal L) r) * m = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  rw [hzero, add_zero]

/-- For a local ring, localizing at the maximal ideal does not change the dimension of the
quotient by a prime. -/
private theorem ringKrullDim_localized_quotient_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    (p : PrimeSpectrum R) :
    ringKrullDim
        (Localization.AtPrime (maximalIdeal R) ⧸
          p.asIdeal.map (algebraMap R (Localization.AtPrime (maximalIdeal R)))) =
      ringKrullDim (R ⧸ p.asIdeal) := by
  let S := (maximalIdeal R).primeCompl
  have hself : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha
  let := hself
  let L := Localization.AtPrime (maximalIdeal R)
  let pL := p.asIdeal.map (algebraMap R L)
  let e : L ≃ₐ[R] R := IsLocalization.algEquiv S L R
  have hmap : pL.map (e : L →+* R) = p.asIdeal := by
    dsimp [pL]
    rw [Ideal.map_map]
    have he : (e : L →+* R).comp (algebraMap R L) = RingHom.id R := by
      ext a
      exact e.commutes a
    rw [he]
    simp
  exact ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv pL p.asIdeal e.toRingEquiv hmap.symm)

/-- A dualizing complex stays dualizing after transport along a ring isomorphism. -/
private theorem isDualizingComplex_of_ringEquiv_aux
    {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T]
    (e : R ≃+* T) (K : DerivedCategory (ModuleCat.{w} R))
    (hK : Dualizing.IsDualizingComplex K) :
    Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars e.toRingHom).obj K) := by
  let : Algebra R T := e.toRingHom.toAlgebra
  let S : Submonoid R := (IsUnit.submonoid T).map e.symm.toRingHom
  let : IsLocalization (IsUnit.submonoid T) T := inferInstance
  let : IsLocalization S T :=
    IsLocalization.isLocalization_of_base_ringEquiv (IsUnit.submonoid T) T e.symm
  exact Dualizing.isDualizingComplex_localization S K hK

/-! ### Arithmetic in the extended integers -/

/-- A finite extended natural number is the integer it names. -/
private theorem enatToEInt_eq_int_toNat {n : ℕ∞} (hn : n ≠ ⊤) :
    enatToEInt n = ((n.toNat : ℤ) : EInt) := by
  cases n with
  | top => exact (hn rfl).elim
  | coe n => rfl

/-- Adding `⊤` on the right of a finite or infinite depth gives `⊤`. -/
private theorem enatToEInt_add_top (n : ℕ∞) :
    enatToEInt n + (⊤ : EInt) = ⊤ := by
  cases n <;> rfl

/-- Adding `⊤` on the left gives `⊤`. -/
private theorem top_add_enatToEInt (n : ℕ∞) :
    (⊤ : EInt) + enatToEInt n = ⊤ := by
  cases n <;> rfl

/-- Moving an integer summand across a weak inequality in the extended integers. -/
private theorem eint_add_int_ge_iff {x : EInt} {s n : ℤ} :
    x + (n : EInt) ≥ (s : EInt) ↔ x ≥ (s - n : EInt) := by
  cases x using WithBotTop.rec with
  | bot => simp
  | top =>
    change (s : EInt) ≤ ⊤ ↔ ⊤ ≥ (s - n : EInt)
    simp
  | coe x =>
    change ((↑((x + n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) ≥
      ((s : WithTop ℤ) : WithBot (WithTop ℤ))) ↔
      ((↑(x : WithTop ℤ) : WithBot (WithTop ℤ)) ≥
        ((s - n : WithTop ℤ) : WithBot (WithTop ℤ)))
    constructor
    · intro h
      apply WithBotTop.coe_le_coe.mpr
      have h0 : ((s : WithTop ℤ) : WithBot (WithTop ℤ)) ≤
          ((x + n : ℤ) : WithTop ℤ) := h
      have h' : s ≤ x + n := WithTop.coe_le_coe.mp <| WithBot.coe_le_coe.mp h0
      omega
    · intro h
      apply WithBotTop.coe_le_coe.mpr
      have h0 : ((s - n : WithTop ℤ) : WithBot (WithTop ℤ)) ≤
          ((x : WithTop ℤ) : WithBot (WithTop ℤ)) := h
      have h' : s - n ≤ x := WithTop.coe_le_coe.mp <| WithBot.coe_le_coe.mp h0
      omega

/-- Moving an integer summand across a strict inequality in the extended integers. -/
private theorem eint_add_int_gt_iff {x : EInt} {s n : ℤ} :
    x + (n : EInt) > (s : EInt) ↔ x > (s - n : EInt) := by
  cases x using WithBotTop.rec with
  | bot => simp
  | top =>
    change (s : EInt) < ⊤ ↔ ⊤ > (s - n : EInt)
    constructor
    · intro _
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (s - n))
    · intro _
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top s)
  | coe x =>
    change ((↑((x + n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) >
      ((s : WithTop ℤ) : WithBot (WithTop ℤ))) ↔
      ((↑(x : WithTop ℤ) : WithBot (WithTop ℤ)) >
        ((s - n : WithTop ℤ) : WithBot (WithTop ℤ)))
    constructor
    · intro h
      apply WithBotTop.coe_lt_coe.mpr
      have h' : s < x + n := WithTop.coe_lt_coe.mp <| WithBot.coe_lt_coe.mp h
      omega
    · intro h
      apply WithBotTop.coe_lt_coe.mpr
      have h' : s - n < x := WithTop.coe_lt_coe.mp <| WithBot.coe_lt_coe.mp h
      omega

/-- Cancelling a common integer summand in a strict inequality. -/
private theorem eint_add_int_gt_cancel {x : EInt} {s n : ℤ}
    (h : x + (n : EInt) > (s + n : EInt)) : x > (s : EInt) := by
  simpa only [add_sub_cancel_right] using (eint_add_int_gt_iff.mp h)

/-! ### Parts (1) and (2) -/

/-- A scalar annihilating a module annihilates its adic completion. -/
private theorem adicCompletion_smul_eq_zero
    {R : Type*} [CommRing R] (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R N]
    {r : R} (h : ∀ n : N, r • n = 0) (t : AdicCompletion I N) : r • t = 0 := by
  ext k
  rw [AdicCompletion.val_smul_apply, AdicCompletion.val_zero_apply]
  obtain ⟨m, hm⟩ :=
    Submodule.Quotient.mk_surjective (I ^ k • ⊤ : Submodule R N) (t.val k)
  rw [← hm, ← Submodule.Quotient.mk_smul, h m]
  simp

/-- The open subscheme `U` of an algebraization situation is a Noetherian scheme. -/
private theorem isNoetherian_toScheme (S : AlgebraizationSituation.{u}) :
    IsNoetherian S.U.toScheme := by
  let : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  let : CompactSpace S.U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (S.U : Set S.X))
  exact (isNoetherian_iff S.U.toScheme).2 ⟨inferInstance, inferInstance⟩

/-- At a point of `U ∩ Y` the completed local ring is local, its maximal ideal is the completed
one, and the completed ideal lies inside it. -/
private theorem completedLocalRing_isLocal_and_ideal_le
    (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) :
    ∃ _ : IsLocalRing (completedLocalRing (idealOnOpen S) y),
      completedMaximalIdeal (idealOnOpen S) y =
          maximalIdeal (completedLocalRing (idealOnOpen S) y) ∧
        completedLocalIdeal (idealOnOpen S) y ≤
          maximalIdeal (completedLocalRing (idealOnOpen S) y) := by
  let : IsNoetherianRing (completedLocalRing (idealOnOpen S) y) :=
    AdicCompletion.isNoetherianRing (IdealSheafData.stalk (idealOnOpen S) y)
  let : IsLocalRing (completedLocalRing (idealOnOpen S) y) :=
    isLocalRing_adicCompletion_of_le_maximalIdeal _ (stalkIdeal_le_maximal S y z hyz)
  have hm : completedMaximalIdeal (idealOnOpen S) y =
      maximalIdeal (completedLocalRing (idealOnOpen S) y) :=
    IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _
      (stalkIdeal_le_maximal S y z hyz) (Ideal.fg_of_isNoetherianRing _))
  refine ⟨inferInstance, hm, ?_⟩
  change (IdealSheafData.stalk (idealOnOpen S) y).map _ ≤ _
  rw [← hm]
  exact Ideal.map_mono (stalkIdeal_le_maximal S y z hyz)

/-- The completion of a complete local ring `R` at an ideal `J`, localized at the maximal ideal,
is again `R`: `R → R_𝔪 → (R_𝔪)^∧` is a ring isomorphism. -/
private theorem exists_ringEquiv_adicCompletion_localization
    {R : Type u} [CommRing R] [IsLocalRing R] (J : Ideal R) [IsAdicComplete J R]
    (q : Ideal R) [q.IsPrime] (hq : q = maximalIdeal R) :
    ∃ _ : IsAdicComplete (J.map (algebraMap R (Localization.AtPrime q)))
        (Localization.AtPrime q),
      Function.Bijective (algebraMap R (Localization.AtPrime q)) ∧
      (maximalIdeal R).map (algebraMap R (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q) ∧
      ∃ e : R ≃+* AdicCompletion (J.map (algebraMap R (Localization.AtPrime q)))
          (Localization.AtPrime q),
        e.toRingHom = (algebraMap (Localization.AtPrime q) _).comp
          (algebraMap R (Localization.AtPrime q)) := by
  subst hq
  let Aq := Localization.AtPrime (maximalIdeal R)
  let : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha
  let e₀ : Aq ≃ₐ[R] R := IsLocalization.algEquiv (maximalIdeal R).primeCompl Aq R
  let e₀r : Aq ≃+* R := e₀.toRingEquiv
  have he₀ : e₀r.symm.toRingHom = algebraMap R Aq := by
    ext x
    apply e₀r.injective
    change e₀ (e₀.symm x) = e₀ (algebraMap R Aq x)
    rw [e₀.apply_symm_apply, e₀.commutes]
    simp
  have hcomplete : IsAdicComplete (J.map (algebraMap R Aq)) Aq := by
    have h := (IsAdicComplete.congr_ringEquiv J e₀r.symm).mpr ‹_›
    change IsAdicComplete (J.map e₀r.symm.toRingHom) Aq at h
    rwa [he₀] at h
  refine ⟨hcomplete, he₀ ▸ e₀r.symm.bijective, ?_, e₀r.symm.trans
    (AdicCompletion.ofAlgEquiv (J.map (algebraMap R Aq))).toRingEquiv, ?_⟩
  · rw [← he₀]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e₀r.symm
  · rw [RingEquiv.toRingHom_trans', he₀]
    rfl

/-- **Stacks Project, Tag 0EJ4 (1).** A coherent `I`-adic system on `U` annihilated by a fixed
power of `I` satisfies the `(a, b)`-inequalities for every pair of bounds, since every formal
stalk then localizes to zero at a prime outside the adic locus and so has infinite depth. -/
@[stacks 0EJ4 "part (1)"]
public theorem satisfiesDepthInequalities_of_annihilated
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hF : ∃ c : ℕ, ∀ n : ℕ,
      _root_.Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple (idealOnOpen S) c
        (F.obj.obj (op n)) = ⊥)
    (a b : ℤ) :
    SatisfiesDepthInequalities S F a b := by
  classical
  obtain ⟨c, hc⟩ := hF
  intro y z hy p hp
  have := isNoetherian_toScheme S
  have hnot : ¬ IdealSheafData.stalk (idealOnOpen S) y ≤
      p.asIdeal.comap (algebraMap (S.U.toScheme.presheaf.stalk y)
        (completedLocalRing (idealOnOpen S) y)) := by
    simpa only [completedLocalIdeal, Ideal.map_le_iff_le_comap] using hp
  obtain ⟨r, hr, hrp⟩ := SetLike.not_le_iff_exists.mp hnot
  have hkill (t : formalStalk F y) : r ^ c • t = 0 := by
    apply Concrete.limit_ext (F.obj ⋙ stalkModuleFunctor y)
    intro n
    change (limit.π (F.obj ⋙ stalkModuleFunctor y) n).hom (r ^ c • t) =
      (limit.π (F.obj ⋙ stalkModuleFunctor y) n).hom 0
    rw [map_smul, map_zero]
    exact idealPowerMultiple_stalk_smul_pow_eq_zero (idealOnOpen S) (F.obj.obj n) c
      (hc n.unop) y hr _
  have hkillM (t : completedStalk (idealOnOpen S) F y) :
      (algebraMap (S.U.toScheme.presheaf.stalk y)
        (completedLocalRing (idealOnOpen S) y) r) ^ c • t = 0 := by
    rw [← map_pow, IsScalarTower.algebraMap_smul]
    exact adicCompletion_smul_eq_zero (IdealSheafData.stalk (idealOnOpen S) y) hkill t
  have hzero (t : LocalizedModule p.asIdeal.primeCompl
      (completedStalk (idealOnOpen S) F y)) : t = 0 := by
    apply LocalizedModule.eq_zero_of_smul_eq_zero
      ((algebraMap (S.U.toScheme.presheaf.stalk y)
        (completedLocalRing (idealOnOpen S) y) r) ^ c)
      (p.asIdeal.primeCompl.pow_mem hrp c)
    induction t using LocalizedModule.induction_on with
    | _ t q =>
      rw [LocalizedModule.smul'_mk, hkillM]
      simp
  let : Subsingleton (LocalizedModule p.asIdeal.primeCompl
      (completedStalk (idealOnOpen S) F y)) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have hdepth : completedStalkDepth (idealOnOpen S) F y p = ⊤ :=
    ite_eq_left (Subsingleton.elim _ _)
  have hdist : depthAddDistance S F y z p = ⊤ := by
    change enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
      enatToEInt (S.distanceToZ z) = ⊤
    rw [hdepth]
    exact top_add_enatToEInt _
  refine ⟨fun _ => Or.inl ?_, fun _ => ?_⟩
  · rw [hdist]
    exact le_top
  · rw [hdist]
    exact lt_top_iff_ne_top.mpr (by simp)

/-- **Stacks Project, Tag 0EJ4 (2).** A coherent `I`-adic system on `U` satisfying the
`(a + 1, b)`-inequalities satisfies the strict `(a, b)`-inequalities: in the case distinguished
by the adic closed fibre the weak bound `a + 1` already beats `a` strictly. -/
@[stacks 0EJ4 "part (2)"]
public theorem satisfiesStrictDepthInequalities_of_succ
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (a b : ℤ)
    (hF : SatisfiesDepthInequalities S F (a + 1) b) :
    SatisfiesStrictDepthInequalities S F a b := by
  classical
  intro y z hy p hp
  have h := hF y z hy p hp
  have ha : (a : EInt) < ((a + 1 : ℤ) : EInt) := by
    change (↑(↑a : WithTop ℤ) : WithBot (WithTop ℤ)) < _
    exact WithBotTop.coe_lt_coe.mpr (by change (a : ℤ) < a + 1; omega)
  by_cases hs : adicClosedFibreThrough (idealOnOpen S) y p =
      {completedMaximalIdeal (idealOnOpen S) y}
  · exact Or.inl (ha.trans (h.2 hs))
  · rcases h.1 hs with h' | h'
    · exact Or.inl (ha.trans_le h')
    · exact Or.inr h'

/-! ### Part (3) -/

/-- The forward implication of part (3): the `(s, s + d)`-inequalities produce, at every point
of `U ∩ Y` of finite distance from `Z`, a bootstrap situation on the completed local data. -/
private theorem depthInequalities_implies_bootstrap
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (s d : ℤ)
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{max u v} S.A),
      Dualizing.IsDualizingComplex K) :
    SatisfiesDepthInequalities S F s (s + d) →
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        S.distanceToZ z ≠ ⊤ →
        ∃ B : BootstrapSituation.{u, u, v},
          B.A = completedLocalRing (idealOnOpen S) y ∧
          HEq B.commRing
            (inferInstance : CommRing (completedLocalRing (idealOnOpen S) y)) ∧
          HEq B.I (completedLocalIdeal (idealOnOpen S) y) ∧
          B.M = completedStalk (idealOnOpen S) F y ∧
          HEq B.addCommGroup
            (inferInstance : AddCommGroup (completedStalk (idealOnOpen S) F y)) ∧
          HEq B.module (inferInstance : Module (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y)) ∧
          HEq B.T {q : PrimeSpectrum (completedLocalRing (idealOnOpen S) y) |
            q.asIdeal = completedMaximalIdeal (idealOnOpen S) y} ∧
          B.s = s - ((S.distanceToZ z).toNat : ℤ) ∧ B.d = d := by
  classical
  intro hF y z hyz hδ
  let R₀ := S.U.toScheme.presheaf.stalk y
  let I₀ := IdealSheafData.stalk (idealOnOpen S) y
  let R := completedLocalRing (idealOnOpen S) y
  let J := completedLocalIdeal (idealOnOpen S) y
  let M := completedStalk (idealOnOpen S) F y
  let n : ℕ := (S.distanceToZ z).toNat
  let m : Ideal R := completedMaximalIdeal (idealOnOpen S) y
  let P : PrimeSpectrum R → Set (Ideal R) := fun q =>
    adicClosedFibreThrough (idealOnOpen S) y q
  let depthVal := fun q : PrimeSpectrum R =>
    enatToEInt (completedStalkDepth (idealOnOpen S) F y q)
  let dimVal := fun q : PrimeSpectrum R => krullDimToEInt (ringKrullDim (R ⧸ q.asIdeal))
  let distVal := enatToEInt (S.distanceToZ z)
  have hdist : distVal = (n : EInt) := enatToEInt_eq_int_toNat (n := S.distanceToZ z) hδ
  have hineq := hF y z hyz
  let : IsNoetherianRing R := AdicCompletion.isNoetherianRing I₀
  obtain ⟨_, hm, hJm⟩ : ∃ _ : IsLocalRing R, m = maximalIdeal R ∧ J ≤ maximalIdeal R :=
    completedLocalRing_isLocal_and_ideal_le S y z hyz
  have := isNoetherian_toScheme S
  let : Module.Finite R M := finite_completedStalk_of_isNoetherian (idealOnOpen S) F y
  have hcdR : _root_.Stacks.LocalCohomology.cohomologicalDimension R J
      (IsNoetherian.noetherian J) ≤ d :=
    completedLocal_cohomologicalDimension_le S y d hcd
  obtain ⟨K, hK⟩ := hdual
  let x₀ : PrimeSpectrum S.A := S.U.ι.base y
  let : Algebra S.A (S.X.presheaf.stalk x₀) :=
    (StructureSheaf.toStalk S.A x₀).hom.toAlgebra
  let : IsLocalization x₀.asIdeal.primeCompl (S.X.presheaf.stalk x₀) := by
    change IsLocalization x₀.asIdeal.primeCompl
      ((structurePresheafInCommRingCat S.A).stalk x₀)
    infer_instance
  have hKloc := Dualizing.isDualizingComplex_localization
    (A := S.A) (B := S.X.presheaf.stalk x₀) x₀.asIdeal.primeCompl K hK
  let f₁ : S.X.presheaf.stalk x₀ →+* R₀ := (S.U.ι.stalkMap y).hom
  have hf₁ : Function.Bijective f₁ :=
    ConcreteCategory.bijective_of_isIso (S.U.ι.stalkMap y)
  let e₁ : S.X.presheaf.stalk x₀ ≃+* R₀ := RingEquiv.ofBijective f₁ hf₁
  have hKR₀ := isDualizingComplex_of_ringEquiv_aux e₁ _ hKloc
  have hKR := Dualizing.isDualizingComplex_adicCompletion I₀ _ hKR₀
  let B : BootstrapSituation.{u, u, v} := {
    A := R
    I := J
    M := M
    T := {q : PrimeSpectrum R | q.asIdeal = m}
    subset_adicLocus := by
      intro q hq
      change J ≤ q.asIdeal
      have hqm : q.asIdeal = maximalIdeal R := by simpa [hm] using hq
      rw [hqm]
      exact hJm
    stableUnderSpecialization := by
      have hT : {q : PrimeSpectrum R | q.asIdeal = m} =
          PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
        ext q
        simp only [Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus]
        constructor
        · intro h
          rw [hm] at h
          rw [h]
        · intro h
          have hqeq : q.asIdeal = maximalIdeal R :=
            le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) h
          rw [hm, hqeq]
      rw [hT]
      exact (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
    s := s - (n : ℤ)
    d := d
    dualizing := ⟨_, hKR⟩
    cohomologicalDimension_le := hcdR
    depth_or_depth_add_dimension := by
      intro q r w hqr hrw hqJ hrJ hrnot hwT
      have hwm : w.asIdeal = maximalIdeal R := by simpa [hm] using hwT
      have hwclosed : w = IsLocalRing.closedPoint R := by
        apply PrimeSpectrum.ext
        simpa [IsLocalRing.closedPoint] using hwm
      subst w
      have hnotSingleton : P q ≠ {m} := by
        intro hsingle
        have hrmem : r.asIdeal ∈ P q := ⟨r.isPrime, hqr, hrJ⟩
        rw [hsingle] at hrmem
        have hrm : r.asIdeal = m := by simpa using hrmem
        have hrT : r ∈ {w : PrimeSpectrum R | w.asIdeal = m} := hrm
        exact hrnot hrT
      have hq := (hineq q hqJ).1 hnotSingleton
      change (depthVal q + distVal ≥ (s : EInt)) ∨
        (depthVal q + dimVal q + distVal > ((s + d : ℤ) : EInt)) at hq
      rcases hq with hdepth | hdim
      · left
        rw [hdist] at hdepth
        have hdepth' : depthVal q + ((n : ℤ) : EInt) ≥ (s : EInt) := hdepth
        exact (eint_add_int_ge_iff (x := depthVal q) (s := s) (n := n)).mp hdepth'
      · right
        rw [hdist] at hdim
        have hdim' : (depthVal q + dimVal q) + ((n : ℤ) : EInt) >
            ((s + d : ℤ) : EInt) := hdim
        have hshift := (eint_add_int_gt_iff (x := depthVal q + dimVal q)
          (s := s + d) (n := (n : ℤ))).mp hdim'
        have hsd : s + d - n = d + (s - n) := by omega
        rw [hsd] at hshift
        have hdimq : krullDimToEInt
            (ringKrullDim
              (Localization.AtPrime (IsLocalRing.closedPoint R).asIdeal ⧸
                q.asIdeal.map
                  (algebraMap R
                    (Localization.AtPrime (IsLocalRing.closedPoint R).asIdeal)))) =
            dimVal q :=
          congrArg krullDimToEInt (ringKrullDim_localized_quotient_eq q)
        convert hshift using 1
        exact congrArg (fun t : EInt => depthVal q + t) hdimq
    completedLocalDepth := by
      intro q hq
      dsimp only
      intro p hp' huniq
      have hqm : q.asIdeal = maximalIdeal R := by simpa [hm] using hq
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := J.map (algebraMap R Aq)
      let Mq := LocalizedModule q.asIdeal.primeCompl M
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      have hRcomplete : IsAdicComplete J R :=
        AdicCompletion.isAdicComplete_self I₀ (Ideal.fg_of_isNoetherianRing I₀)
      obtain ⟨_, -, hmaxAq, e, hecomp⟩ :=
        exists_ringEquiv_adicCompletion_localization J q.asIdeal hqm
      let e₂ : Aq ≃ₐ[Aq] A' := AdicCompletion.ofAlgEquiv Iq
      have hmapJ : J.map e.toRingHom = I' := by
        rw [hecomp, ← Ideal.map_map]
      have hmapm : (maximalIdeal R).map e.toRingHom = m' := by
        rw [hecomp, ← Ideal.map_map, hmaxAq]
      let pLoc : Ideal Aq := p.asIdeal.comap e₂.toRingEquiv.toRingHom
      have : pLoc.IsPrime := Ideal.IsPrime.comap _
      have hcontractmap : (pLoc.comap (algebraMap R Aq)).map (algebraMap R Aq) = pLoc :=
        IsLocalization.map_under q.asIdeal.primeCompl Aq pLoc
      have hmapLocP : pLoc.map (algebraMap Aq A') = p.asIdeal := by
        dsimp [pLoc]
        exact Ideal.map_comap_of_surjective _ e₂.toRingEquiv.surjective _
      have hpOrigImage : (pLoc.comap (algebraMap R Aq)).map e.toRingHom =
          p.asIdeal := by
        rw [hecomp, ← Ideal.map_map, hcontractmap, hmapLocP]
      let p₀ : Ideal R := pLoc.comap (algebraMap R Aq)
      have : p₀.IsPrime := Ideal.IsPrime.comap _
      change ¬ I' ≤ p.asIdeal at hp'
      change {r' : Ideal A' | r'.IsPrime ∧ p.asIdeal ≤ r' ∧ I' ≤ r'} = {m'} at huniq
      have hIqmax : Iq ≤ maximalIdeal Aq := (Ideal.map_mono hJm).trans hmaxAq.le
      let : IsLocalRing A' := isLocalRing_adicCompletion_of_le_maximalIdeal Iq hIqmax
      have hmapP : p₀.map e.toRingHom = p.asIdeal := hpOrigImage
      have hp₀J : ¬ J ≤ p₀ := by
        intro h
        apply hp'
        rw [← hmapJ, ← hmapP]
        exact Ideal.map_mono h
      have hcm (L : Ideal R) : (L.map e.toRingHom).comap e.toRingHom = L :=
        Ideal.comap_map_of_bijective _ e.bijective
      have hP₀ : {r : Ideal R | r.IsPrime ∧ p₀ ≤ r ∧ J ≤ r} =
          {maximalIdeal R} := by
        ext r
        constructor
        · intro hr
          have hr' : r.map e.toRingHom ∈
              {r' : Ideal A' | r'.IsPrime ∧ p.asIdeal ≤ r' ∧ I' ≤ r'} := by
            let : r.IsPrime := hr.1
            have : (r.map e.toRingHom).IsPrime := by
              change (Ideal.map e r).IsPrime
              exact Ideal.map_isPrime_of_equiv e
            refine ⟨inferInstance, ?_, ?_⟩
            · rw [← hmapP]
              exact Ideal.map_mono hr.2.1
            · rw [← hmapJ]
              exact Ideal.map_mono hr.2.2
          rw [huniq] at hr'
          have hrmap : r.map e.toRingHom = m' := by simpa using hr'
          calc
            r = (r.map e.toRingHom).comap e.toRingHom := (hcm r).symm
            _ = ((maximalIdeal R).map e.toRingHom).comap e.toRingHom := by
                rw [hrmap, hmapm]
            _ = maximalIdeal R := hcm (maximalIdeal R)
        · intro hr
          have hrm : r = maximalIdeal R := by simpa using hr
          subst r
          have : (maximalIdeal R).IsPrime := (IsLocalRing.maximalIdeal.isMaximal R).isPrime
          exact ⟨inferInstance,
            IsLocalRing.le_maximalIdeal (inferInstance : p₀.IsPrime).ne_top, hJm⟩
      have hP₀m : P ⟨p₀, inferInstance⟩ = {m} := by
        change {r : Ideal R | r.IsPrime ∧ p₀ ≤ r ∧ J ≤ r} = {m}
        rw [hm]
        exact hP₀
      have hpineq := (hineq ⟨p₀, inferInstance⟩ hp₀J).2 hP₀m
      change depthVal ⟨p₀, inferInstance⟩ + distVal > (s : EInt) at hpineq
      rw [hdist] at hpineq
      have hstrict : depthVal ⟨p₀, inferInstance⟩ > (s - (n : ℤ) : EInt) :=
        (eint_add_int_gt_iff (x := depthVal ⟨p₀, inferInstance⟩)
          (s := s) (n := (n : ℤ))).mp hpineq
      have : p.asIdeal.LiesOver pLoc := ⟨rfl⟩
      have hdepthLE := Module.depth_localized_adicCompletion_le
        (A := Aq) Iq (M := Mq) pLoc p.asIdeal
      have hdepthEq := depth_localizedModule_localizationAtPrime
        (M := M) q.asIdeal pLoc
      have hrawLE :
          Module.depth (Localization.AtPrime p₀) (maximalIdeal (Localization.AtPrime p₀))
              (LocalizedModule p₀.primeCompl M) ≤
            Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl (AdicCompletion Iq Mq)) :=
        hdepthEq.le.trans hdepthLE
      have hdepthIntLE : depthVal ⟨p₀, inferInstance⟩ ≤
          enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl (AdicCompletion Iq Mq))) :=
        enatToEInt_mono hrawLE
      exact lt_of_lt_of_le hstrict hdepthIntLE
  }
  refine ⟨B, rfl, ?_, ?_, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · change HEq (inferInstance : CommRing R) (inferInstance : CommRing R)
    exact HEq.rfl
  · change HEq J J
    rfl
  · change HEq (inferInstance : AddCommGroup M) (inferInstance : AddCommGroup M)
    exact HEq.rfl
  · change HEq (inferInstance : Module R M) (inferInstance : Module R M)
    exact HEq.rfl
  · change HEq {q : PrimeSpectrum R | q.asIdeal = m}
      {q : PrimeSpectrum R | q.asIdeal = m}
    rfl

/-- **Stacks Project, Tag 0EJ4 (3).** If `cd(A, I) ≤ d` and `A` has a dualizing complex, then a
coherent `I`-adic system on `U` satisfies the `(s, s + d)`-inequalities exactly when, at every
point `y` of `U ∩ Y` with `δ^Y_Z(y)` finite, the completed local ring, the ideal `I𝒪_{X,y}^∧`,
the singleton `{𝔪_y^∧}`, the formal stalk `ℱ_y^∧` and the bounds `s - δ^Y_Z(y)` and `d` form a
bootstrap situation. -/
@[stacks 0EJ4 "part (3)"]
public theorem satisfiesDepthInequalities_iff_bootstrapSituation
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (s d : ℤ)
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{max u v} S.A),
      Dualizing.IsDualizingComplex K) :
    SatisfiesDepthInequalities S F s (s + d) ↔
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        S.distanceToZ z ≠ ⊤ →
        ∃ B : BootstrapSituation.{u, u, v},
          B.A = completedLocalRing (idealOnOpen S) y ∧
          HEq B.commRing
            (inferInstance : CommRing (completedLocalRing (idealOnOpen S) y)) ∧
          HEq B.I (completedLocalIdeal (idealOnOpen S) y) ∧
          B.M = completedStalk (idealOnOpen S) F y ∧
          HEq B.addCommGroup
            (inferInstance : AddCommGroup (completedStalk (idealOnOpen S) F y)) ∧
          HEq B.module (inferInstance : Module (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y)) ∧
          HEq B.T {q : PrimeSpectrum (completedLocalRing (idealOnOpen S) y) |
            q.asIdeal = completedMaximalIdeal (idealOnOpen S) y} ∧
          B.s = s - ((S.distanceToZ z).toNat : ℤ) ∧ B.d = d := by
  classical
  constructor
  · exact depthInequalities_implies_bootstrap S F s d hcd hdual
  · intro hB y z hyz p hp
    let R₀ := S.U.toScheme.presheaf.stalk y
    let I₀ := IdealSheafData.stalk (idealOnOpen S) y
    let R := completedLocalRing (idealOnOpen S) y
    let J := completedLocalIdeal (idealOnOpen S) y
    let M := completedStalk (idealOnOpen S) F y
    let n : ℕ := (S.distanceToZ z).toNat
    let m : Ideal R := completedMaximalIdeal (idealOnOpen S) y
    let depthVal := enatToEInt (completedStalkDepth (idealOnOpen S) F y p)
    let dimVal := krullDimToEInt (ringKrullDim (R ⧸ p.asIdeal))
    let distVal := enatToEInt (S.distanceToZ z)
    by_cases hδtop : S.distanceToZ z = ⊤
    · have htop : depthVal + distVal = ⊤ := by
        change _ + enatToEInt (S.distanceToZ z) = ⊤
        rw [hδtop]
        exact enatToEInt_add_top _
      refine ⟨fun _ => Or.inl ?_, fun _ => ?_⟩
      · change depthVal + distVal ≥ (s : EInt)
        rw [htop]
        exact le_top
      · change depthVal + distVal > (s : EInt)
        rw [htop]
        exact lt_top_iff_ne_top.mpr (by simp)
    have hδ : S.distanceToZ z ≠ ⊤ := hδtop
    have hdist : distVal = (n : EInt) := enatToEInt_eq_int_toNat (n := S.distanceToZ z) hδ
    let : IsNoetherianRing R := AdicCompletion.isNoetherianRing I₀
    obtain ⟨_, hm, hJm⟩ : ∃ _ : IsLocalRing R, m = maximalIdeal R ∧ J ≤ maximalIdeal R :=
      completedLocalRing_isLocal_and_ideal_le S y z hyz
    have := isNoetherian_toScheme S
    let : Module.Finite R M := finite_completedStalk_of_isNoetherian (idealOnOpen S) F y
    obtain ⟨B₀, hBA, hBcomm, hBJ, hBM, hBadd, hBmodule, hBT, hsB, hdB⟩ :=
      hB y z hyz hδ
    cases B₀
    rename_i A bc bn bi bm ba bmod bf bt bsub bstable bs bd bdual bcd bdepth bcompleted
    cases hBA
    cases hBcomm
    cases hBJ
    cases hBM
    cases hBadd
    cases hBmodule
    let B : BootstrapSituation.{u, u, v} := {
      A := R
      commRing := inferInstance
      isNoetherianRing := bn
      I := J
      M := M
      addCommGroup := inferInstance
      module := inferInstance
      finite := bf
      T := bt
      subset_adicLocus := bsub
      stableUnderSpecialization := bstable
      s := bs
      d := bd
      dualizing := bdual
      cohomologicalDimension_le := bcd
      depth_or_depth_add_dimension := bdepth
      completedLocalDepth := bcompleted }
    have hBJ' : B.I = J := rfl
    have hBT' : B.T = {q : PrimeSpectrum R | q.asIdeal = m} := eq_of_heq hBT
    refine ⟨fun hne => ?_, fun heq => ?_⟩
    · have hsingleton : {q : Ideal R | q.IsPrime ∧ p.asIdeal ≤ q ∧ J ≤ q} ≠ {m} := hne
      have hmP : m ∈ {q : Ideal R | q.IsPrime ∧ p.asIdeal ≤ q ∧ J ≤ q} := by
        rw [hm]
        exact ⟨(IsLocalRing.maximalIdeal.isMaximal R).isPrime,
          IsLocalRing.le_maximalIdeal p.isPrime.ne_top, hJm⟩
      have hex : ∃ r : Ideal R,
          r ∈ {q : Ideal R | q.IsPrime ∧ p.asIdeal ≤ q ∧ J ≤ q} ∧ r ≠ m := by
        by_contra h
        apply hsingleton
        ext r
        constructor
        · intro hr
          by_cases hrm : r = m
          · simp [hrm]
          · exact False.elim (h ⟨r, hr, hrm⟩)
        · intro hr
          have hrm : r = m := by simpa using hr
          subst r
          exact hmP
      obtain ⟨r, hrP, hrm⟩ := hex
      let r' : PrimeSpectrum R := ⟨r, hrP.1⟩
      let q : PrimeSpectrum R := IsLocalRing.closedPoint R
      have hq : q.asIdeal = maximalIdeal R := by
        simp [q, IsLocalRing.closedPoint]
      have hrle : r ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hrP.1.ne_top
      have hrnotT : r' ∉ B.T := by
        rw [hBT']
        change r ≠ m
        exact hrm
      have hqT : q ∈ B.T := by
        rw [hBT']
        simp [hq, hm]
      have hpnot : p ∉ PrimeSpectrum.zeroLocus (B.I : Set R) := by
        rw [PrimeSpectrum.mem_zeroLocus]
        simpa [hBJ'] using hp
      have hrV : r' ∈ PrimeSpectrum.zeroLocus (B.I : Set R) := by
        rw [PrimeSpectrum.mem_zeroLocus]
        exact hrP.2.2
      have hdepthB := B.depth_or_depth_add_dimension
        p r' q hrP.2.1 hrle hpnot hrV hrnotT hqT
      change (depthVal ≥ (B.s : EInt)) ∨
        (depthVal + krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)))) >
          ((B.d + B.s : ℤ) : EInt)) at hdepthB
      rcases hdepthB with hdepth | hdim
      · left
        change depthVal + distVal ≥ (s : EInt)
        rw [hsB] at hdepth
        have hdepth' : depthVal + (n : EInt) ≥ (s : EInt) :=
          (eint_add_int_ge_iff (x := depthVal) (s := s) (n := (n : ℤ))).mpr hdepth
        simpa [hdist] using hdepth'
      · right
        change depthVal + dimVal + distVal > ((s + d : ℤ) : EInt)
        have hdimq : krullDimToEInt
            (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
              p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)))) = dimVal := by
          change krullDimToEInt
            (ringKrullDim (Localization.AtPrime (maximalIdeal R) ⧸
              p.asIdeal.map (algebraMap R (Localization.AtPrime (maximalIdeal R))))) = dimVal
          exact congrArg krullDimToEInt (ringKrullDim_localized_quotient_eq p)
        rw [hdimq, hsB, hdB] at hdim
        have hsd : s + d - (n : ℤ) = d + (s - (n : ℤ)) := by omega
        have hdim' : depthVal + dimVal > ((s + d - (n : ℤ) : ℤ) : EInt) := by
          rw [hsd]
          exact hdim
        have hshift : depthVal + dimVal + (n : EInt) > ((s + d : ℤ) : EInt) :=
          (eint_add_int_gt_iff (x := depthVal + dimVal)
            (s := s + d) (n := (n : ℤ))).mpr hdim'
        simpa [hdist, add_assoc] using hshift
    · have hsingleton : {q : Ideal R | q.IsPrime ∧ p.asIdeal ≤ q ∧ J ≤ q} = {m} := heq
      let q : PrimeSpectrum R := IsLocalRing.closedPoint R
      have hqT : q ∈ B.T := by
        rw [hBT']
        exact hm.symm
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := J.map (algebraMap R Aq)
      let Mq := LocalizedModule q.asIdeal.primeCompl M
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      have hRcomplete : IsAdicComplete J R :=
        AdicCompletion.isAdicComplete_self I₀ (Ideal.fg_of_isNoetherianRing I₀)
      obtain ⟨_, hbij, hmaxAq, e, hecomp⟩ :=
        exists_ringEquiv_adicCompletion_localization J q.asIdeal rfl
      let e₂ : Aq ≃ₐ[Aq] A' := AdicCompletion.ofAlgEquiv Iq
      have hmapJ : J.map e.toRingHom = I' := by
        rw [hecomp, ← Ideal.map_map]
      have hmapm : m.map e.toRingHom = m' := by
        rw [hm, hecomp, ← Ideal.map_map, hmaxAq]
      let pLoc := p.asIdeal.map (algebraMap R Aq)
      have : pLoc.IsPrime := Ideal.map_isPrime_of_equiv (RingEquiv.ofBijective _ hbij)
      let p' : PrimeSpectrum A' := ⟨pLoc.map (algebraMap Aq A'), by
        change (pLoc.map e₂.toRingEquiv.toRingHom).IsPrime
        exact Ideal.map_isPrime_of_equiv e₂.toRingEquiv⟩
      have : p'.asIdeal.IsPrime := p'.isPrime
      have hmapP : p.asIdeal.map e.toRingHom = p'.asIdeal := by
        rw [hecomp, ← Ideal.map_map]
      have hcm (L : Ideal R) : (L.map e.toRingHom).comap e.toRingHom = L :=
        Ideal.comap_map_of_bijective _ e.bijective
      have hp' : ¬ I' ≤ p'.asIdeal := by
        intro h
        apply hp
        have h' := Ideal.comap_mono (f := e.toRingHom) h
        rw [← hmapJ, ← hmapP, hcm, hcm] at h'
        exact h'
      have huniq : {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} =
          {m'} := by
        ext r'
        constructor
        · intro hr'
          have hmem : r'.comap e.toRingHom ∈
              {w : Ideal R | w.IsPrime ∧ p.asIdeal ≤ w ∧ J ≤ w} := by
            let : r'.IsPrime := hr'.1
            refine ⟨Ideal.IsPrime.comap _, ?_, ?_⟩
            · exact Ideal.map_le_iff_le_comap.mp (hmapP.symm ▸ hr'.2.1)
            · exact Ideal.map_le_iff_le_comap.mp (hmapJ.symm ▸ hr'.2.2)
          rw [hsingleton] at hmem
          have hrm : r'.comap e.toRingHom = m := by simpa using hmem
          have hrmap := Ideal.map_comap_of_surjective e.toRingHom e.surjective r'
          rw [hrm, hmapm] at hrmap
          exact hrmap.symm
        · intro hr'
          have hrm : r' = m' := Set.mem_singleton_iff.mp hr'
          subst r'
          rw [← hmapm, ← hmapP, ← hmapJ]
          have : m.IsPrime := hm ▸ (IsLocalRing.maximalIdeal.isMaximal R).isPrime
          exact ⟨Ideal.map_isPrime_of_equiv e,
            Ideal.map_mono (by simpa only [hm] using
              IsLocalRing.le_maximalIdeal p.isPrime.ne_top),
            Ideal.map_mono (by simpa only [hm] using hJm)⟩
      have hdepthB := B.completedLocalDepth q hqT p' hp' huniq
      have hcontractLoc : p'.asIdeal.comap (algebraMap Aq A') = pLoc :=
        Ideal.comap_map_of_bijective _ e₂.bijective
      have hcontract : pLoc.comap (algebraMap R Aq) = p.asIdeal :=
        Ideal.comap_map_of_bijective _ hbij
      have hdepthEq : Module.depth (Localization.AtPrime p'.asIdeal)
          (maximalIdeal (Localization.AtPrime p'.asIdeal))
          (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq)) =
            Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M) := by
        rw [depth_localized_adicCompletion_eq_of_complete Iq p'.asIdeal]
        exact (depth_localizedModule_congr_aux _ pLoc hcontractLoc).trans
          ((depth_localizedModule_localizationAtPrime (M := M) q.asIdeal pLoc).symm.trans
            (depth_localizedModule_congr_aux _ p.asIdeal hcontract))
      change enatToEInt
        (Module.depth (Localization.AtPrime p'.asIdeal)
          (maximalIdeal (Localization.AtPrime p'.asIdeal))
          (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq))) > (B.s : EInt)
        at hdepthB
      rw [hdepthEq, hsB] at hdepthB
      change depthVal + distVal > (s : EInt)
      rw [hdist]
      exact (eint_add_int_gt_iff (x := depthVal) (s := s) (n := (n : ℤ))).mpr hdepthB

/-! ### Part (4) -/

/-- **Stacks Project, Tag 0EJ4 (4).** If `cd(A, I) ≤ d` and `A` has a dualizing complex, then
the strict `(s, s + d)`-inequalities imply the ordinary `(s, s + d)`-inequalities: in the case
distinguished by the adic closed fibre the prime is isolated in the adic locus, so
`dim(𝒪_{X,y}^∧/𝔭) ≤ cd(𝒪_{X,y}^∧, I𝒪_{X,y}^∧) ≤ d` and the bound `s + d` on the sum implies
the bound `s` on the depth alone. The isolated-prime bound used for this is
`Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'`, which discharges the
local case of Stacks 0BFR on the completion of `𝒪_{X,y}^∧/𝔭` itself rather than taking it as a
hypothesis. -/
@[stacks 0EJ4 "part (4)"]
public theorem satisfiesDepthInequalities_of_strict
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (s d : ℤ)
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (_hdual : ∃ K : DerivedCategory (ModuleCat.{max u v} S.A),
      Dualizing.IsDualizingComplex K)
    (hF : SatisfiesStrictDepthInequalities S F s (s + d)) :
    SatisfiesDepthInequalities S F s (s + d) := by
  classical
  intro y z hy p hp
  let R₀ := S.U.toScheme.presheaf.stalk y
  let I₀ := IdealSheafData.stalk (idealOnOpen S) y
  let R := completedLocalRing (idealOnOpen S) y
  let J := completedLocalIdeal (idealOnOpen S) y
  let m : Ideal R := completedMaximalIdeal (idealOnOpen S) y
  let depthVal := enatToEInt (completedStalkDepth (idealOnOpen S) F y p)
  let distVal := enatToEInt (S.distanceToZ z)
  let dimVal := krullDimToEInt (ringKrullDim (R ⧸ p.asIdeal))
  have h := hF y z hy p hp
  change (depthVal + distVal > (s : EInt)) ∨
    (depthVal + dimVal + distVal > ((s + d : ℤ) : EInt)) at h
  refine ⟨fun _ => ?_, fun heq => ?_⟩
  · rcases h with h' | h'
    · exact Or.inl (le_of_lt h')
    · exact Or.inr h'
  have hsingleton : {q : Ideal R | q.IsPrime ∧ p.asIdeal ≤ q ∧ J ≤ q} = {m} := heq
  have := isNoetherian_toScheme S
  let : IsNoetherianRing R := AdicCompletion.isNoetherianRing I₀
  obtain ⟨_, hm, hJm⟩ : ∃ _ : IsLocalRing R, m = maximalIdeal R ∧ J ≤ maximalIdeal R :=
    completedLocalRing_isLocal_and_ideal_le S y z hy
  have hzero : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) ∩
      PrimeSpectrum.zeroLocus (J : Set R) = {IsLocalRing.closedPoint R} := by
    ext q
    constructor
    · intro hq
      change p.asIdeal ≤ q.asIdeal ∧ J ≤ q.asIdeal at hq
      have hmem : q.asIdeal ∈
          {r : Ideal R | r.IsPrime ∧ p.asIdeal ≤ r ∧ J ≤ r} :=
        ⟨q.isPrime, hq.1, hq.2⟩
      rw [hsingleton] at hmem
      have hqeq : q.asIdeal = m := by simpa using hmem
      apply PrimeSpectrum.ext
      simpa [IsLocalRing.closedPoint, hm] using hqeq
    · intro hq
      have hq' : q = IsLocalRing.closedPoint R := by simpa using hq
      subst q
      simp only [PrimeSpectrum.mem_zeroLocus, IsLocalRing.closedPoint,
        Set.mem_inter_iff, SetLike.coe_subset_coe, hJm, and_true]
      exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  have hcdR := completedLocal_cohomologicalDimension_le S y d hcd
  have : Nontrivial (R ⧸ p.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
  let : IsLocalRing (R ⧸ p.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal)
      Ideal.Quotient.mk_surjective
  have hdim_le : ringKrullDim (R ⧸ p.asIdeal) ≤
      (maximalIdeal (R ⧸ p.asIdeal)).spanFinrank := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr
      ((IsLocalRing.maximalIdeal (R ⧸ p.asIdeal)).height_le_spanFinrank
        (IsLocalRing.maximalIdeal.isMaximal (R ⧸ p.asIdeal)).ne_top)
  have hdimBot : ringKrullDim (R ⧸ p.asIdeal) ≠ ⊥ := by
    intro hbot
    exact (not_subsingleton_iff_nontrivial.mpr inferInstance)
      (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  have hdimTop : ringKrullDim (R ⧸ p.asIdeal) ≠ ⊤ :=
    ne_of_lt (hdim_le.trans_lt (by
      change ((Submodule.spanFinrank (maximalIdeal (R ⧸ p.asIdeal)) : ℕ∞) : WithBot ℕ∞) <
        ((⊤ : ℕ∞) : WithBot ℕ∞)
      exact WithBot.coe_lt_coe.mpr
        (ENat.natCast_lt_top (Submodule.spanFinrank (maximalIdeal (R ⧸ p.asIdeal))))))
  have : p.asIdeal.IsPrime := p.isPrime
  have hc_le : dimVal ≤ (d : EInt) := by
    cases hdim : ringKrullDim (R ⧸ p.asIdeal) with
    | bot => exact (hdimBot hdim).elim
    | coe k =>
      cases k with
      | top => exact (hdimTop hdim).elim
      | coe k =>
        simp only [dimVal, krullDimToEInt, hdim]
        have hbound' : (k : ℤ) ≤
            _root_.Stacks.LocalCohomology.cohomologicalDimension R J
              (IsNoetherian.noetherian J) :=
          _root_.Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'
            R p.asIdeal J (IsNoetherian.noetherian J) hzero k
            (by rw [hdim]; norm_cast)
        exact WithBotTop.coe_le_coe.mpr (hbound'.trans hcdR)
  change depthVal + distVal > (s : EInt)
  rcases h with h' | h'
  · exact h'
  · have hle : depthVal + dimVal + distVal ≤
        depthVal + (d : EInt) + distVal := by
      gcongr
    have hlt := lt_of_lt_of_le h' hle
    have hshift : (depthVal + distVal) + (d : EInt) >
        (s : EInt) + (d : EInt) := by
      convert hlt using 1 <;> ac_rfl
    exact eint_add_int_gt_cancel hshift

/-! ### All four parts together -/

/-- **Stacks Project, Tag 0EJ4.** The four elementary properties of the depth–distance
inequalities, as one statement about a coherent `I`-adic system `(ℱₙ)` on `U` in an
algebraization situation.

1. If `(ℱₙ)` is annihilated by a power of `I`, it satisfies the `(a, b)`-inequalities for every
   pair of bounds.
2. If `(ℱₙ)` satisfies the `(a + 1, b)`-inequalities, it satisfies the strict
   `(a, b)`-inequalities.

If moreover `cd(A, I) ≤ d` and `A` has a dualizing complex, then

3. `(ℱₙ)` satisfies the `(s, s + d)`-inequalities exactly when, at every point `y` of `U ∩ Y`
   with `δ^Y_Z(y)` finite, the completed local ring, the ideal `I𝒪_{X,y}^∧`, the singleton
   `{𝔪_y^∧}`, the formal stalk `ℱ_y^∧` and the bounds `s - δ^Y_Z(y)` and `d` form a bootstrap
   situation, and
4. the strict `(s, s + d)`-inequalities imply the ordinary `(s, s + d)`-inequalities.

Parts (1) and (2) are stated here under no hypothesis beyond the situation itself, exactly as
the source states them; the hypotheses `cd(A, I) ≤ d` and the existence of a dualizing complex
are carried only by parts (3) and (4), which is where the source introduces them. The four
parts are `Stacks.Algebraization.satisfiesDepthInequalities_of_annihilated`,
`Stacks.Algebraization.satisfiesStrictDepthInequalities_of_succ`,
`Stacks.Algebraization.satisfiesDepthInequalities_iff_bootstrapSituation` and
`Stacks.Algebraization.satisfiesDepthInequalities_of_strict`. -/
@[stacks 0EJ4]
public theorem satisfiesDepthInequalities_elementary_properties
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    ((∃ c : ℕ, ∀ n : ℕ,
        _root_.Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple (idealOnOpen S) c
          (F.obj.obj (op n)) = ⊥) →
      ∀ a b : ℤ, SatisfiesDepthInequalities S F a b) ∧
    (∀ a b : ℤ, SatisfiesDepthInequalities S F (a + 1) b →
      SatisfiesStrictDepthInequalities S F a b) ∧
    (∀ s d : ℤ,
      _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
          (Ideal.fg_of_isNoetherianRing S.I) ≤ d →
      (∃ K : DerivedCategory (ModuleCat.{max u v} S.A), Dualizing.IsDualizingComplex K) →
      (SatisfiesDepthInequalities S F s (s + d) ↔
          ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
            S.distanceToZ z ≠ ⊤ →
            ∃ B : BootstrapSituation.{u, u, v},
              B.A = completedLocalRing (idealOnOpen S) y ∧
              HEq B.commRing
                (inferInstance : CommRing (completedLocalRing (idealOnOpen S) y)) ∧
              HEq B.I (completedLocalIdeal (idealOnOpen S) y) ∧
              B.M = completedStalk (idealOnOpen S) F y ∧
              HEq B.addCommGroup
                (inferInstance : AddCommGroup (completedStalk (idealOnOpen S) F y)) ∧
              HEq B.module (inferInstance : Module (completedLocalRing (idealOnOpen S) y)
                (completedStalk (idealOnOpen S) F y)) ∧
              HEq B.T {q : PrimeSpectrum (completedLocalRing (idealOnOpen S) y) |
                q.asIdeal = completedMaximalIdeal (idealOnOpen S) y} ∧
              B.s = s - ((S.distanceToZ z).toNat : ℤ) ∧ B.d = d) ∧
        (SatisfiesStrictDepthInequalities S F s (s + d) →
          SatisfiesDepthInequalities S F s (s + d))) :=
  ⟨fun hF a b => satisfiesDepthInequalities_of_annihilated S F hF a b,
    fun a b hF => satisfiesStrictDepthInequalities_of_succ S F a b hF,
    fun s d hcd hdual =>
      ⟨satisfiesDepthInequalities_iff_bootstrapSituation.{u, v} S F s d hcd hdual,
        satisfiesDepthInequalities_of_strict.{u, v} S F s d hcd hdual⟩⟩

end Stacks.Algebraization

end
