module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekAffineChartsRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrictComposition
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# Transitivity of `H⁰(f_new^! 𝒪_Y)|_V ≅ H⁰((V → Y)_new^! 𝒪_Y)`

In Situation [Stacks, Tag 0AU4], `H⁰` at the standard model commutes with restriction along an
open immersion compatibly with composites, `ι^*(f_new^! M) ≅ (ι ≫ f)_new^! M` is natural in the
dualizing complex, and for opens `W ⊆ V` of `X` the identification of `H⁰(f_new^! 𝒪_Y)|_W` is
that of `H⁰(f_new^! 𝒪_Y)|_V`, restricted to `W`, followed by the one for `W ⊆ V`.

## References

* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Duality

open _root_.AlgebraicGeometry
open Stacks.Duality.TwistedInverseImageDuality (Std pull pullCompIso_hom_app_rfl)

universe u

/-- The chase behind `homologyPullIsoOfOpenImmersion_comp`. -/
theorem homologyPullIsoOfOpenImmersion_comp_chase {𝒜 ℬ 𝒟 ℰ : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒟] [Category ℰ] (Hh : 𝒟 ⥤ 𝒜) (Hb : ℰ ⥤ ℬ) (G : ℰ ⥤ 𝒟) (R : ℬ ⥤ 𝒜)
    {d₀ d₁ d₂ : 𝒟} {e₀ e₁ : ℰ} {m₀ : 𝒜} {n₁ : ℬ}
    (γI : d₂ ≅ d₀) (mabI : Hh.obj d₂ ≅ m₀) (c : m₀ ⟶ R.obj n₁) (pI i' : d₁ ≅ d₀)
    (aI : G.obj e₀ ≅ d₁) (maI : Hh.obj (G.obj e₀) ≅ R.obj (Hb.obj e₀)) (bI : e₁ ≅ e₀)
    (mbI : Hb.obj e₁ ≅ n₁) (θ : G.obj e₁ ⟶ d₂) (maI' : Hh.obj (G.obj e₁) ≅ R.obj (Hb.obj e₁))
    (e : R.obj n₁ ⟶ m₀)
    (hi : pI.hom = i'.hom) (H1a : γI.inv = i'.inv ≫ aI.inv ≫ G.map bI.inv ≫ θ)
    (C : Hh.map θ ≫ mabI.hom = maI'.hom ≫ R.map mbI.hom ≫ e) (he : e ≫ c = 𝟙 _)
    (N : Hh.map (G.map bI.inv) ≫ maI'.hom = maI.hom ≫ R.map (Hb.map bI.inv)) :
    ((Hh.mapIso γI.symm).hom ≫ mabI.hom) ≫ c =
      (Hh.mapIso pI.symm).hom ≫ ((Hh.mapIso aI.symm).hom ≫ maI.hom) ≫
        R.map ((Hb.mapIso bI.symm).hom ≫ mbI.hom) := by
  have hinv : pI.inv = i'.inv := congrArg Iso.inv (Iso.ext hi)
  simp only [Functor.mapIso_hom, Iso.symm_hom, H1a, hinv]
  simp only [Functor.map_comp, Category.assoc, C, he, Category.comp_id]
  rw [reassoc_of% N]

attribute [local instance 10000] HasDerivedCategory.standard


/-- **`H⁰` commutes with restriction along a composite of open immersions in two steps.** -/
theorem homologyPullIsoOfOpenImmersion_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] (K : Std C) :
    homologyPullIsoOfOpenImmersion (a ≫ b) K ≪≫
        (Scheme.Modules.restrictFunctorComp a b).app _ =
      (@DerivedCategory.homologyFunctor A.Modules _ _
        (PerfectApproximation.standardModel A) 0).mapIso
          ((UpperShriekDuality.pullCompIso a b (a ≫ b) rfl).app K).symm ≪≫
        homologyPullIsoOfOpenImmersion a ((pull b).obj K) ≪≫
        (Scheme.Modules.restrictFunctor a).mapIso (homologyPullIsoOfOpenImmersion b K) := by
  ext1
  simp only [homologyPullIsoOfOpenImmersion, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  exact homologyPullIsoOfOpenImmersion_comp_chase
    (@DerivedCategory.homologyFunctor A.Modules _ _ (PerfectApproximation.standardModel A) 0)
    (@DerivedCategory.homologyFunctor B.Modules _ _ (PerfectApproximation.standardModel B) 0)
    (Scheme.Modules.restrictFunctor a).mapDerivedCategory (Scheme.Modules.restrictFunctor a)
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback (a ≫ b)).app K)
    (((Scheme.Modules.restrictFunctor (a ≫ b)).mapDerivedCategoryHomologyIso 0).app K)
    ((Scheme.Modules.restrictFunctorComp a b).hom.app _)
    ((UpperShriekDuality.pullCompIso a b (a ≫ b) rfl).app K)
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
      b.toLRSHom.toShHom).app K)
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback a).app ((pull b).obj K))
    (((Scheme.Modules.restrictFunctor a).mapDerivedCategoryHomologyIso 0).app ((pull b).obj K))
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback b).app K)
    (((Scheme.Modules.restrictFunctor b).mapDerivedCategoryHomologyIso 0).app K)
    ((Functor.mapDerivedCategoryCompIsoOfCompIso (Scheme.Modules.restrictFunctorComp a b).symm).hom.app K)
    (((Scheme.Modules.restrictFunctor a).mapDerivedCategoryHomologyIso 0).app
      ((Scheme.Modules.restrictFunctor b).mapDerivedCategory.obj K))
    ((Scheme.Modules.restrictFunctorComp a b).inv.app _)
    (pullCompIso_hom_app_rfl a b K)
    (NatTrans.congr_app (Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_comp a b) K)
    (Scheme.Modules.homologyFunctor_map_mapDerivedCategoryCompIso_restrictFunctorComp a b K)
    ((Scheme.Modules.restrictFunctorComp a b).inv_hom_id_app _)
    (((Scheme.Modules.restrictFunctor a).mapDerivedCategoryHomologyIso 0).hom.naturality _)

end Stacks.Duality

namespace Stacks.Duality

universe u

open _root_.AlgebraicGeometry Opposite

open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Duality.UpperShriekDuality (pullCompIso)
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

variable {V X Y : Scheme.{u}} (ι : V ⟶ X) [IsOpenImmersion ι]

/-- The components of `dualIntoMapIso`. -/
theorem relativeDualMapIso_hom_app_eq {Z : Scheme.{u}} {ω ω' : Std Z} (e : ω ≅ ω') (P : (Std Z)ᵒᵖ) :
    (dualIntoMapIso e).hom.app P = ((sheafHom Z).obj P).map e.hom :=
  rfl

/-- Two naturality squares pasted. -/
theorem comp_comp_eq_comp_comp_of_naturality {𝒞 : Type*} [Category 𝒞] {a b c d e f' : 𝒞}
    (z : a ⟶ b) (p' : b ⟶ d) (c' : d ⟶ f') (p : a ⟶ c) (m : c ⟶ d) (cc : c ⟶ e) (m' : e ⟶ f')
    (N1 : z ≫ p' = p ≫ m) (N2 : m ≫ c' = cc ≫ m') : z ≫ p' ≫ c' = (p ≫ cc) ≫ m' := by
  rw [← Category.assoc, N1, Category.assoc, N2, Category.assoc]

/-- **`ι^* ∘ f_new^! ≅ k_new^!` is natural in the dualizing complex upstairs.** -/
theorem fNewShriekRestrictIso_naturality_dualizing (f : X ⟶ Y) (k : V ⟶ Y) (e : ι ≫ f = k)
    {ω ω' : Std X} (s : ω ≅ ω') (ωY M : Std Y) :
    (pull ι).map ((dualIntoMapIso s).hom.app ((pull f).op.obj ((dualInto ωY).rightOp.obj M))) ≫
        (fNewShriekRestrictIso ι f k e ω' ωY).hom.app M =
      (fNewShriekRestrictIso ι f k e ω ωY).hom.app M ≫
        (dualIntoMapIso ((pull ι).mapIso s)).hom.app
          ((pull k).op.obj ((dualInto ωY).rightOp.obj M)) := by
  simp only [fNewShriekRestrictIso_hom_app, dualInto_map_natIsoOp_inv_app,
    relativeDualMapIso_hom_app_eq]
  rw [pullDualIso_hom_app, pullDualIso_hom_app]
  exact comp_comp_eq_comp_comp_of_naturality _ _ _ _ _ _ _
    (pullSheafHomMap_naturality_right ι _ s.hom) (((sheafHom V).map _).naturality _)

/-- Three images under a functor composed. -/
theorem functor_map_comp₃_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {a b c d : 𝒞}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) (w : a ⟶ d) (h : x ≫ y ≫ z = w) :
    F.map x ≫ F.map y ≫ F.map z = F.map w := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- The chase behind `fNewShriekRestrictIso_trans_relativeDualMapIso`. -/
theorem fNewShriekRestrictIso_trans_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (P : 𝒟 ⥤ 𝒞)
    {d₀ d₁ d₂ : 𝒟} {c₀ c₁ c₂ c₃ c₄ : 𝒞} (i : c₀ ⟶ P.obj d₀) (a : d₀ ⟶ d₁) (b : d₁ ⟶ d₂)
    (c : P.obj d₂ ⟶ c₁) (d : c₁ ⟶ c₂) (a' : c₀ ⟶ c₃) (d' : c₃ ⟶ c₂) (c₀' : P.obj d₁ ⟶ c₄)
    (n : c₄ ⟶ c₁) (t : c₃ ⟶ c₄) (Nat : P.map b ≫ c = c₀' ≫ n)
    (T1 : a' ≫ t = i ≫ P.map a ≫ c₀') (R : t ≫ n ≫ d = d') :
    i ≫ P.map (a ≫ b) ≫ c ≫ d = a' ≫ d' := by
  rw [← R, P.map_comp, Category.assoc, reassoc_of% Nat, ← reassoc_of% T1]

variable {W : Scheme.{u}}

/-- **`f_new^!` restricted in two steps, with the dualizing complexes identified.** -/
theorem fNewShriekRestrictIso_trans_relativeDualMapIso (ι : W ⟶ V) (uV : V ⟶ X) (uW : W ⟶ X)
    [IsOpenImmersion ι] [IsOpenImmersion uV] [IsOpenImmersion uW] (h : ι ≫ uV = uW) (f : X ⟶ Y)
    (gV : V ⟶ Y) (gW : W ⟶ Y) (eV : uV ≫ f = gV) (eW : uW ≫ f = gW) (eι : ι ≫ gV = gW)
    (ωX : Std X) (ωY : Std Y) {ωV : Std V} {ωW : Std W} (sV : ωV ≅ (pull uV).obj ωX)
    (sW : ωW ≅ (pull uW).obj ωX) (M : Std Y) :
    (pullCompIso ι uV uW h).inv.app _ ≫
        (pull ι).map ((fNewShriekRestrictIso uV f gV eV ωX ωY).hom.app M ≫
          (dualIntoMapIso sV.symm).hom.app ((pull gV).op.obj ((dualInto ωY).rightOp.obj M))) ≫
        (fNewShriekRestrictIso ι gV gW eι ωV ωY).hom.app M ≫
        (dualIntoMapIso (sW ≪≫ ((pullCompIso ι uV uW h).app ωX).symm ≪≫
          (pull ι).mapIso sV.symm).symm).hom.app ((pull gW).op.obj ((dualInto ωY).rightOp.obj M)) =
      (fNewShriekRestrictIso uW f gW eW ωX ωY).hom.app M ≫
        (dualIntoMapIso sW.symm).hom.app ((pull gW).op.obj ((dualInto ωY).rightOp.obj M)) := by
  refine fNewShriekRestrictIso_trans_chase (pull ι) _ _ _ _ _ _ _ _ _ _
    (fNewShriekRestrictIso_naturality_dualizing ι gV gW eι sV.symm ωY M)
    (fNewShriekRestrictIso_comp ι uV uW h f gV gW eV eW eι ωX ωY M) ?_
  simp only [relativeDualMapIso_inv_app_eq, relativeDualMapIso_hom_app_eq]
  exact functor_map_comp₃_eq _ _ _ _ _ (by simp)

/-- The chase behind `homologyPullIsoOfOpenImmersion_naturality`. -/
theorem homologyPullIsoOfOpenImmersion_naturality_chase {𝒜 ℬ 𝒟 ℰ : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒟] [Category ℰ] (H : 𝒟 ⥤ 𝒜) (H' : ℰ ⥤ ℬ) (G : ℰ ⥤ 𝒟) (R : ℬ ⥤ 𝒜)
    (P : ℰ ⥤ 𝒟) {e e' : ℰ} (φ : e ⟶ e') (x : P.obj e ⟶ G.obj e) (x' : P.obj e' ⟶ G.obj e')
    (m : H.obj (G.obj e) ⟶ R.obj (H'.obj e)) (m' : H.obj (G.obj e') ⟶ R.obj (H'.obj e'))
    (N1 : P.map φ ≫ x' = x ≫ G.map φ) (N2 : H.map (G.map φ) ≫ m' = m ≫ R.map (H'.map φ)) :
    H.map (P.map φ) ≫ H.map x' ≫ m' = (H.map x ≫ m) ≫ R.map (H'.map φ) := by
  rw [← H.map_comp_assoc, N1, H.map_comp, Category.assoc, N2, Category.assoc]

/-- `H⁰` commutes with restriction along an open immersion, naturally. -/
theorem homologyPullIsoOfOpenImmersion_naturality {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K K' : Std X} (φ : K ⟶ K') :
    (@DerivedCategory.homologyFunctor U.Modules _ _ (PerfectApproximation.standardModel U) 0).map
        ((pull j).map φ) ≫ (homologyPullIsoOfOpenImmersion j K').hom =
      (homologyPullIsoOfOpenImmersion j K).hom ≫ (Scheme.Modules.restrictFunctor j).map
        ((@DerivedCategory.homologyFunctor X.Modules _ _
          (PerfectApproximation.standardModel X) 0).map φ) := by
  simp only [homologyPullIsoOfOpenImmersion, Iso.trans_hom]
  exact homologyPullIsoOfOpenImmersion_naturality_chase _ _ _ _ _ φ _ _ _ _
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv.naturality φ)
    (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso 0).hom.naturality φ)

/-- `homologyPullIsoOfOpenImmersion_comp` along any `a ≫ b = k`. -/
theorem homologyPullIsoOfOpenImmersion_comp' {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    {k : A ⟶ C} [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion k] (w : a ≫ b = k)
    (K : Std C) :
    homologyPullIsoOfOpenImmersion k K ≪≫ (Scheme.Modules.restrictFunctorCongr w).symm.app _ ≪≫
        (Scheme.Modules.restrictFunctorComp a b).app _ =
      (@DerivedCategory.homologyFunctor A.Modules _ _
        (PerfectApproximation.standardModel A) 0).mapIso
          ((UpperShriekDuality.pullCompIso a b k w).app K).symm ≪≫
        homologyPullIsoOfOpenImmersion a ((pull b).obj K) ≪≫
        (Scheme.Modules.restrictFunctor a).mapIso (homologyPullIsoOfOpenImmersion b K) := by
  subst w
  have hc : (Scheme.Modules.restrictFunctorCongr (rfl : a ≫ b = a ≫ b)).symm.app
      ((@DerivedCategory.homologyFunctor C.Modules _ _ (PerfectApproximation.standardModel C) 0).obj
        K) = Iso.refl _ := by
    ext1
    refine Scheme.Modules.hom_ext _ _ (fun U => ?_)
    simp [Scheme.Modules.restrictFunctorCongr_inv_app_app]
    rfl
  rw [hc, Iso.refl_trans]
  exact homologyPullIsoOfOpenImmersion_comp a b K

end Stacks.Duality

namespace Stacks.Duality

universe u

open _root_.AlgebraicGeometry Opposite
open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh plusCoh_le_qcoh plusCoh_iff
  pull stdMonoidal stdSymmetric stdMonoidalClosed)

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
  [LocallyQuasiFinite f]

/-- `ω_W^• ≅ L(W → V)^* ω_V^•` for opens `W ⊆ V`, through `ω_X^•|_W` and `ω_X^•|_V`. -/
def stdComplexRestrictLEIso {V W : X.Opens} (hWV : W ≤ V) :
    stdComplex c (𝒦X.restrict W) ≅ (pull (X.homOfLE hWV)).obj (stdComplex c (𝒦X.restrict V)) :=
  stdComplexRestrictIso c 𝒦X W ≪≫
    ((UpperShriekDuality.pullCompIso (X.homOfLE hWV) V.ι W.ι (X.homOfLE_ι hWV)).app _).symm ≪≫
    (pull (X.homOfLE hWV)).mapIso (stdComplexRestrictIso c 𝒦X V).symm

/-- The chase behind `newShriekStructureSheafZerothRestrictIso_trans`. -/
theorem newShriekStructureSheafZerothRestrictIso_trans_chase {𝒜 ℬ 𝒟 ℰ : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒟] [Category ℰ] (H : 𝒟 ⥤ 𝒜) (H' : ℰ ⥤ ℬ) (R : ℬ ⥤ 𝒜) (P : ℰ ⥤ 𝒟)
    {a₀ a₁ : 𝒜} {b₀ : ℬ} {e₀ e₁ : ℰ} {d₀ d₂ : 𝒟} (c₁ : a₀ ⟶ a₁) (c₂ : a₁ ⟶ R.obj b₀)
    (hV : H'.obj e₀ ≅ b₀) (φV : e₀ ≅ e₁) (hι : H.obj (P.obj e₁) ≅ R.obj (H'.obj e₁))
    (ψ : P.obj e₁ ≅ d₂) (hW : H.obj d₀ ≅ a₀) (φW : d₀ ≅ d₂) (pc : P.obj e₀ ≅ d₀)
    (hι₀ : H.obj (P.obj e₀) ≅ R.obj (H'.obj e₀))
    (H1 : hW.hom ≫ c₁ ≫ c₂ = (H.mapIso pc.symm).hom ≫ hι₀.hom ≫ R.map hV.hom)
    (Nat : H.map (P.map φV.hom) ≫ hι.hom = hι₀.hom ≫ R.map (H'.map φV.hom))
    (core : pc.inv ≫ P.map φV.hom ≫ ψ.hom = φW.hom) :
    c₁ ≫ c₂ ≫ R.map (hV.inv ≫ (H'.mapIso φV).hom) ≫ hι.inv ≫ (H.mapIso ψ).hom =
      hW.inv ≫ (H.mapIso φW).hom := by
  rw [← cancel_epi hW.hom, Iso.hom_inv_id_assoc, reassoc_of% H1]
  simp only [Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc hV.hom, Iso.hom_inv_id, R.map_id, Category.id_comp, ← reassoc_of% Nat,
    Iso.hom_inv_id_assoc, ← H.map_comp, ← H.map_comp, core]

omit [LocallyQuasiFinite f] in
open UpperShriekDuality TwistedInverseImageDuality in
open CategoryTheory.MonoidalClosed (dualInto) in
attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed in
/-- **(G1) `H⁰(f_new^! 𝒪_Y)|_V ≅ H⁰((V → Y)_new^! 𝒪_Y)` is transitive** for `W ⊆ V`. -/
theorem newShriekStructureSheafZerothRestrictIso_trans {V W : X.Opens} (hWV : W ≤ V) :
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWV)).symm.app
        (newShriekStructureSheafZeroth c f 𝒦X 𝒦Y) ≪≫
      (Scheme.Modules.restrictFunctorComp (X.homOfLE hWV) V.ι).app
        (newShriekStructureSheafZeroth c f 𝒦X 𝒦Y) ≪≫
      (Scheme.Modules.restrictFunctor (X.homOfLE hWV)).mapIso
        (newShriekStructureSheafZerothRestrictIso c f 𝒦X 𝒦Y V) ≪≫
      ((homologyPullIsoOfOpenImmersion (X.homOfLE hWV) _).symm ≪≫
        (@DerivedCategory.homologyFunctor W.toScheme.Modules _ _
          (PerfectApproximation.standardModel W.toScheme) 0).mapIso
          ((fNewShriekRestrictIso (X.homOfLE hWV) (V.ι ≫ f) (W.ι ≫ f)
              (by rw [← Category.assoc, Scheme.homOfLE_ι]) (stdComplex c (𝒦X.restrict V))
              (stdComplex c 𝒦Y)).app (structureStd Y) ≪≫
            (Functor.isoWhiskerLeft (dualInto (stdComplex c 𝒦Y)).rightOp
              (Functor.isoWhiskerLeft (pull (W.ι ≫ f)).op
                (dualIntoMapIso (stdComplexRestrictLEIso c 𝒦X hWV).symm))).app
              (structureStd Y))) =
      newShriekStructureSheafZerothRestrictIso c f 𝒦X 𝒦Y W := by
  ext1
  simp only [newShriekStructureSheafZerothRestrictIso, homologyPullIso_eq, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  refine newShriekStructureSheafZerothRestrictIso_trans_chase
    (@DerivedCategory.homologyFunctor W.toScheme.Modules _ _
      (PerfectApproximation.standardModel W.toScheme) 0)
    (@DerivedCategory.homologyFunctor V.toScheme.Modules _ _
      (PerfectApproximation.standardModel V.toScheme) 0)
    (Scheme.Modules.restrictFunctor (X.homOfLE hWV)) (pull (X.homOfLE hWV))
    ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWV)).inv.app
      (newShriekStructureSheafZeroth c f 𝒦X 𝒦Y))
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hWV) V.ι).hom.app
      (newShriekStructureSheafZeroth c f 𝒦X 𝒦Y))
    (homologyPullIsoOfOpenImmersion V.ι
      ((fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (structureStd Y)))
    ((fNewShriekRestrictIso V.ι f (V.ι ≫ f) rfl (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).app
        (structureStd Y) ≪≫
      (Functor.isoWhiskerLeft ((dualInto (stdComplex c 𝒦Y)).rightOp ⋙ (pull (V.ι ≫ f)).op)
        (dualIntoMapIso (stdComplexRestrictIso c 𝒦X V).symm)).app (structureStd Y))
    (homologyPullIsoOfOpenImmersion (X.homOfLE hWV)
      ((fNewShriekStd (V.ι ≫ f) (stdComplex c (𝒦X.restrict V)) (stdComplex c 𝒦Y)).obj
        (structureStd Y)))
    ((fNewShriekRestrictIso (X.homOfLE hWV) (V.ι ≫ f) (W.ι ≫ f)
        (by rw [← Category.assoc, Scheme.homOfLE_ι]) (stdComplex c (𝒦X.restrict V))
        (stdComplex c 𝒦Y)).app (structureStd Y) ≪≫
      (Functor.isoWhiskerLeft (dualInto (stdComplex c 𝒦Y)).rightOp
        (Functor.isoWhiskerLeft (pull (W.ι ≫ f)).op
          (dualIntoMapIso (stdComplexRestrictLEIso c 𝒦X hWV).symm))).app (structureStd Y))
    (homologyPullIsoOfOpenImmersion W.ι
      ((fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (structureStd Y)))
    ((fNewShriekRestrictIso W.ι f (W.ι ≫ f) rfl (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).app
        (structureStd Y) ≪≫
      (Functor.isoWhiskerLeft ((dualInto (stdComplex c 𝒦Y)).rightOp ⋙ (pull (W.ι ≫ f)).op)
        (dualIntoMapIso (stdComplexRestrictIso c 𝒦X W).symm)).app (structureStd Y))
    ((UpperShriekDuality.pullCompIso (X.homOfLE hWV) V.ι W.ι (X.homOfLE_ι hWV)).app
      ((fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (structureStd Y)))
    (homologyPullIsoOfOpenImmersion (X.homOfLE hWV) ((pull V.ι).obj
      ((fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (structureStd Y)))) ?_ ?_ ?_
  · exact congrArg Iso.hom (homologyPullIsoOfOpenImmersion_comp' (X.homOfLE hWV) V.ι
      (X.homOfLE_ι hWV)
      ((fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (structureStd Y)))
  · exact homologyPullIsoOfOpenImmersion_naturality (X.homOfLE hWV) _
  · exact fNewShriekRestrictIso_trans_relativeDualMapIso (X.homOfLE hWV) V.ι W.ι (X.homOfLE_ι hWV) f
      (V.ι ≫ f) (W.ι ≫ f) rfl rfl _ (stdComplex c 𝒦X) (stdComplex c 𝒦Y)
      (stdComplexRestrictIso c 𝒦X V) (stdComplexRestrictIso c 𝒦X W) (structureStd Y)

end NormalizedOnOpens

end Stacks.Duality
