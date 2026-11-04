module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantSequenceDatum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperConstantCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmallUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale cohomology of `𝐆_a` is the cohomology of the structure sheaf, with its Frobenius

For a scheme `X` the étale cohomology of `𝐆_a` (the sheaf of global functions on the small étale
site) is the cohomology of the structure sheaf, in every degree:

  `H ^ n (X_étale, 𝐆_a) ≃ H ^ n (X, 𝒪_X)`,

and this identification is compatible with multiplication by global functions. For `X` over a field
`k` of characteristic `p` it is therefore `k`-linear, so the map induced on `H ^ n (X, 𝒪_X)` by the
Frobenius `x ↦ x ^ p` of `𝐆_a` is `p`-semilinear, and the Artin–Schreier map becomes `F - 1`. That
is the datum `Stacks.ArtinSchreier.TopDegreeFrobeniusComparison`, constructed here as
`Stacks.ArtinSchreier.structureSheafTopDegreeFrobeniusComparison`, in every degree.

## Main definitions

* `Stacks.ArtinSchreier.zariskiPushforwardAdditiveIso`: `ε_* 𝐆_a = 𝒪_X` for
  `ε : X_étale ⟶ X_Zar`.
* `Stacks.ArtinSchreier.additiveSheafBaseHIso`: [Stacks, Tag 03P2] for `𝐆_a` at coefficients
  `AddCommGrpCat.{u}`, `H ^ n (X_étale, 𝐆_a) ≅ H ^ n (X, 𝒪_X)`.
* `Stacks.ArtinSchreier.additiveSheafHEquiv`: the same at coefficients `AddCommGrpCat.{u + 1}`,
  through `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`.
* `Stacks.ArtinSchreier.additiveSheafCohomologyOverFieldEquiv`: the same with
  `AlgebraicGeometry.cohomologyOverField` on the right.
* `Stacks.ArtinSchreier.structureSheafTopDegreeFrobeniusComparison`: the Frobenius comparison.

## Main results

* `Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso_naturality`: the pushforward
  collapse is natural in the sheaf.
* `Stacks.ArtinSchreier.additiveSheafCohomologyOverFieldEquiv_smul`: the comparison is
  `k`-linear.

## Implementation notes

The Frobenius of `𝒪_X` is not `𝒪_X`-linear, so it is not transported through the module side of the
comparison: the Frobenius of `H ^ n (X, 𝒪_X)` is *defined* by transport from the étale side, where
it is induced by the endomorphism `Stacks.ArtinSchreier.frobeniusMap` of `𝐆_a`. Its semilinearity
needs only that the comparison is natural for multiplication by a global function, which is an
`𝒪_X`-linear endomorphism of `𝒪_X`, and that on `𝐆_a` multiplication by `a` followed by Frobenius
is Frobenius followed by multiplication by `a ^ p`.

On the small étale site, instance search for enough injectives and Grothendieck abelianness at
coefficients `AddCommGrpCat.{u}` meets the instance indexed by `max (u + 1) v` first and gets stuck
on its universe constraint, so the instances at `u` are raised in priority for this file.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J)
* [Stacks Project, Tag 0A3P](https://stacks.math.columbia.edu/tag/0A3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.Cohomology.BiggerSite

universe v₁ u₁ u₁'

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁'} [Category.{v₁} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{v₁}] [HasSheafify K AddCommGrpCat.{v₁}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v₁} J K).Additive]
  [PreservesFiniteLimits (u.sheafPushforwardContinuous AddCommGrpCat.{v₁} J K)]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v₁} J K).PreservesInjectiveObjects]
  [HasExt.{v₁} (Sheaf J AddCommGrpCat.{v₁})] [HasExt.{v₁} (Sheaf K AddCommGrpCat.{v₁})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v₁})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{v₁})]

/-- **The collapse of cohomology along a restriction is natural in the sheaf.** -/
theorem sheafCohomologyPushforwardIso_naturality {F G : Sheaf K AddCommGrpCat.{v₁}} (g : F ⟶ G)
    (T : C) (i : ℕ)
    (hF : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v₁} J K).rightDerived q).obj F))
    (hG : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v₁} J K).rightDerived q).obj G)) :
    ((Sheaf.cohomologyPresheafFunctor J i).map
        ((u.sheafPushforwardContinuous AddCommGrpCat.{v₁} J K).map g)).app (op T) ≫
      (sheafCohomologyPushforwardIso J K u G T i hG).hom =
    (sheafCohomologyPushforwardIso J K u F T i hF).hom ≫
      ((Sheaf.cohomologyPresheafFunctor K i).map g).app (op (u.obj T)) := by
  simp only [sheafCohomologyPushforwardIso, rightDerivedSectionsCollapseIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc, RightDerivedEdgeIso.edgeAppIso_hom]
  rw [FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections_inv_naturality,
    ← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc,
    reassoc_of% (FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections_hom_naturality _ _ _ _)]
  rfl

end Stacks.Cohomology.BiggerSite

namespace Stacks.ArtinSchreier

variable (X : Scheme.{u})

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

attribute [local instance 3000] AlgebraicGeometry.enoughInjectives_sheaf_smallEtaleTopology
  AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt

/-- The image of a global function of `X` on an étale `X`-scheme. -/
abbrev pullTop {X : Scheme.{u}} (U : X.Etale) (a : Γ(X, ⊤)) : Γ(U.left, ⊤) :=
  U.hom.appTop a

/-- The image on `U` of a global function of `X`, pulled back along `g : V ⟶ U`, is its image on
`V`. -/
theorem pullTop_map {X : Scheme.{u}} {U V : X.Etale} (g : V ⟶ U) (a : Γ(X, ⊤)) :
    g.left.appTop (pullTop U a) = pullTop V a := by
  rw [pullTop, pullTop, ← MorphismProperty.Over.w g, Scheme.Hom.comp_appTop]
  rfl

/-- Multiplication by a global function on `𝐆_a` at coefficients `AddCommGrpCat.{u}`. -/
def additiveSheafBaseSmul (a : Γ(X, ⊤)) : additiveSheafBase X ⟶ additiveSheafBase X :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mulRight (pullTop U.unop a) : Γ(U.unop.left, ⊤) →+ Γ(U.unop.left, ⊤))
     naturality := fun U V g => by
        ext (x : Γ(U.unop.left, ⊤))
        change g.unop.left.appTop x * pullTop V.unop a =
          g.unop.left.appTop (x * pullTop U.unop a)
        rw [map_mul, pullTop_map] }⟩

/-- Multiplication by a global function on `𝐆_a` at coefficients `AddCommGrpCat.{u + 1}`: the
universe lift of `additiveSheafBaseSmul`. -/
def additiveSheafSmul (a : Γ(X, ⊤)) : additiveSheaf.{u, u + 1} X ⟶ additiveSheaf.{u, u + 1} X :=
  (additiveSheafBaseUliftIso X).inv ≫
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
      (additiveSheafBaseSmul X a) ≫ (additiveSheafBaseUliftIso X).hom

/-- `additiveSheafSmul` on sections. -/
theorem additiveSheafSmul_app_ofSection (a : Γ(X, ⊤)) (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (additiveSheafSmul X a).hom.app (op U) (ofSection.{u, u + 1} x) =
      ofSection.{u, u + 1} (x * pullTop U a) :=
  rfl

/-- **Frobenius is semilinear for the multiplication by global functions**: on sections,
`(x * a) ^ p = x ^ p * a ^ p`. -/
theorem additiveSheafSmul_comp_frobeniusMap {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (a : Γ(X, ⊤)) :
    additiveSheafSmul X a ≫ frobeniusMap.{u, u + 1} X hp hX =
      frobeniusMap.{u, u + 1} X hp hX ≫ additiveSheafSmul X (a ^ p) := by
  ext U x
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, u + 1} (X := X) (U := U.unop) x
  change ofSection.{u, u + 1} ((x * pullTop U.unop a) ^ p) =
    ofSection.{u, u + 1} (x ^ p * pullTop U.unop (a ^ p))
  rw [mul_pow, pullTop, pullTop, map_pow]

/-- **`ε_* 𝐆_a = 𝒪_X`**: the direct image along `ε : X_étale ⟶ X_Zar` of `𝐆_a` is the abelian sheaf
underlying the structure module, its sections over an open `V` being `Γ(V, ⊤) = Γ(X, V)`
(`AlgebraicGeometry.Scheme.restrictFunctorΓ`). -/
def zariskiPushforwardAdditiveIso :
    (smallEtaleZariskiPushforward X).obj (additiveSheafBase X) ≅
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight X.restrictFunctorΓ
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))

/-- **The comparison `ε_* 𝐆_a = 𝒪_X` intertwines the two multiplications by a global function.** -/
theorem zariskiPushforwardAdditiveIso_hom_smul (a : Γ(X, ⊤)) :
    (smallEtaleZariskiPushforward X).map (additiveSheafBaseSmul X a) ≫
        (zariskiPushforwardAdditiveIso X).hom =
      (zariskiPushforwardAdditiveIso X).hom ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map
          (globalSmul a (SheafOfModules.unit X.ringCatSheaf)) := by
  ext V x
  change Γ(Scheme.Opens.toScheme V.unop, ⊤) at x
  have h1 : ((smallEtaleZariskiPushforward X).map (additiveSheafBaseSmul X a) ≫
      (zariskiPushforwardAdditiveIso X).hom).hom.app V x =
        (Scheme.Opens.topIso V.unop).hom (x * (Scheme.Opens.ι V.unop).appTop a) := rfl
  have h2 : ((zariskiPushforwardAdditiveIso X).hom ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map
      (globalSmul a (SheafOfModules.unit X.ringCatSheaf))).hom.app V x =
        (globalSmul a (SheafOfModules.unit X.ringCatSheaf)).app V.unop
          ((Scheme.Opens.topIso V.unop).hom x) := rfl
  have hr : (Scheme.Opens.topIso V.unop).hom ((Scheme.Opens.ι V.unop).appTop a) =
      restrictTop a V.unop := by
    rw [Scheme.Opens.topIso_hom, Scheme.Hom.appTop, Scheme.Opens.ι_app, restrictTop]
    refine (ConcreteCategory.comp_apply _ _ a).symm.trans ?_
    exact congrArg (fun h : Γ(X, ⊤) ⟶ Γ(X, V.unop) => h a)
      ((X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _)))
  rw [h1, h2]
  refine Eq.trans ?_ (globalSmul_app a _ V.unop _).symm
  rw [map_mul, hr, mul_comm]
  rfl

section Positive

variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- **[Stacks, Tag 03P2] for `𝐆_a`, at coefficients `AddCommGrpCat.{u}`**: in every degree,
`H ^ n (X_étale, 𝐆_a) ≅ H ^ n (X, 𝒪_X)`, the right side the right derived functor of global
sections of modules. The steps are the passage from global cohomology to cohomology over the final
object `(opensToEtale X).obj ⊤`, the pushforward collapse along `ε : X_étale ⟶ X_Zar` (its higher
direct images vanishing), `ε_* 𝐆_a = 𝒪_X`, and the comparison of [Stacks, Tag 03FD] of the derived
sections of modules with those of the underlying abelian sheaf. -/
@[sga "4 VII 2.1" "special case"]
def additiveSheafBaseHIso (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u, u} (additiveSheafBase X) n) ≅
      Hgroup X.ringCatSheaf ⊤ n (SheafOfModules.unit X.ringCatSheaf) :=
  (Stacks.Cohomology.TerminalCohomology.h'IsoH X.smallEtaleTopology (additiveSheafBase X)
      n _ (isTerminal_opensToEtale_top X)).symm ≪≫
    (Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
      (Opens.grothendieckTopology X) (Scheme.smallEtaleTopology X) (opensToEtale X)
      (additiveSheafBase X) ⊤ n
      (fun q hq _ => isZero_rightDerived_pushforward_additiveSheafBase X q hq)).symm ≪≫
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).mapIso
      (zariskiPushforwardAdditiveIso X)).app (op ⊤) ≪≫
    Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (Opens.grothendieckTopology X) _ n ⊤ ≪≫
    ((ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X)
      X.ringCatSheaf ⊤ n).app (SheafOfModules.unit X.ringCatSheaf)).symm

/-- **`additiveSheafBaseHIso` intertwines multiplication by a global function.** -/
theorem additiveSheafBaseHIso_naturality (a : Γ(X, ⊤)) (n : ℕ) :
    AddCommGrpCat.ofHom (Sheaf.H.map (additiveSheafBaseSmul X a) n) ≫
        (additiveSheafBaseHIso X n).hom =
      (additiveSheafBaseHIso X n).hom ≫
        (Hfunctor X.ringCatSheaf ⊤ n).map (globalSmul a (SheafOfModules.unit X.ringCatSheaf)) := by
  have hF := fun q (hq : 1 ≤ q) (_ : q ≤ n) =>
    isZero_rightDerived_pushforward_additiveSheafBase X q hq
  have h1 : AddCommGrpCat.ofHom (Sheaf.H.map (additiveSheafBaseSmul X a) n) ≫
      (Stacks.Cohomology.TerminalCohomology.h'IsoH X.smallEtaleTopology (additiveSheafBase X)
        n _ (isTerminal_opensToEtale_top X)).inv =
      (Stacks.Cohomology.TerminalCohomology.h'IsoH X.smallEtaleTopology (additiveSheafBase X)
        n _ (isTerminal_opensToEtale_top X)).inv ≫
      ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map
        (additiveSheafBaseSmul X a)).app (op ((opensToEtale X).obj ⊤)) :=
    ((extFunctor n).mapIso (Stacks.Cohomology.TerminalCohomology.freeOfTerminalIsoConstantSheaf
      X.smallEtaleTopology _ (isTerminal_opensToEtale_top X)).symm.op).inv.naturality
        (additiveSheafBaseSmul X a)
  have h2 := Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso_naturality
    (Opens.grothendieckTopology X) (Scheme.smallEtaleTopology X) (opensToEtale X)
    (additiveSheafBaseSmul X a) ⊤ n hF hF
  have h2' : ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map
        (additiveSheafBaseSmul X a)).app (op ((opensToEtale X).obj ⊤)) ≫
      (Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
        (Opens.grothendieckTopology X) (Scheme.smallEtaleTopology X) (opensToEtale X)
        (additiveSheafBase X) ⊤ n hF).inv =
      (Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
        (Opens.grothendieckTopology X) (Scheme.smallEtaleTopology X) (opensToEtale X)
        (additiveSheafBase X) ⊤ n hF).inv ≫
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
        ((smallEtaleZariskiPushforward X).map (additiveSheafBaseSmul X a))).app (op ⊤) := by
    rw [Iso.comp_inv_eq, Category.assoc, h2, Iso.inv_hom_id_assoc]
  have h3 : ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
        ((smallEtaleZariskiPushforward X).map (additiveSheafBaseSmul X a))).app (op ⊤) ≫
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).mapIso
        (zariskiPushforwardAdditiveIso X)).app (op ⊤)).hom =
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).mapIso
        (zariskiPushforwardAdditiveIso X)).app (op ⊤)).hom ≫
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
          (globalSmul a (SheafOfModules.unit X.ringCatSheaf)))).app (op ⊤) := by
    rw [Iso.app_hom, Functor.mapIso_hom, ← NatTrans.comp_app, ← NatTrans.comp_app,
      ← Functor.map_comp, ← Functor.map_comp, zariskiPushforwardAdditiveIso_hom_smul]
  have h4 :=
    Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections_hom_naturality
      (Opens.grothendieckTopology X) ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (globalSmul a (SheafOfModules.unit X.ringCatSheaf))) n ⊤
  have h5 := (ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X)
    X.ringCatSheaf ⊤ n).inv.naturality (globalSmul a (SheafOfModules.unit X.ringCatSheaf))
  simp only [additiveSheafBaseHIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2', reassoc_of% h3, reassoc_of% h4]
  exact congrArg _ (congrArg _ (congrArg _ (congrArg _ h5)))

end Positive

section Lift

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The étale cohomology of `𝐆_a` is the cohomology of the structure sheaf**, in every degree:
`H ^ n (X_étale, 𝐆_a) ≃ H ^ n (X, 𝒪_X)`, the left side at coefficients `AddCommGrpCat.{u + 1}` in
an arbitrary `Ext` universe. This is `additiveSheafBaseHIso` after raising the coefficient universe
(`Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`). -/
def additiveSheafHEquiv (n : ℕ) :
    Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n ≃+
      Hgroup X.ringCatSheaf ⊤ n (SheafOfModules.unit X.ringCatSheaf) :=
  haveI : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  letI : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  haveI := (etaleUlift_properties.{u, u, u + 1} X).1
  haveI := (etaleUlift_properties.{u, u, u + 1} X).2
  (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr (additiveSheafBaseUliftIso X).symm n).trans <|
  (Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv.{u, u, u + 1, w} X.smallEtaleTopology
      (additiveSheafBase X) n).symm.trans
    (additiveSheafBaseHIso X n).addCommGroupIsoToAddEquiv

/-- **`additiveSheafHEquiv` intertwines multiplication by a global function.** -/
theorem additiveSheafHEquiv_smul (a : Γ(X, ⊤)) (n : ℕ)
    (x : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n) :
    additiveSheafHEquiv X n (Sheaf.H.map (additiveSheafSmul X a) n x) =
      (Hfunctor X.ringCatSheaf ⊤ n).map (globalSmul a (SheafOfModules.unit X.ringCatSheaf))
        (additiveSheafHEquiv X n x) := by
  have : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  let : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  have := (etaleUlift_properties.{u, u, u + 1} X).1
  have := (etaleUlift_properties.{u, u, u + 1} X).2
  let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : L.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits L :=
    Stacks.Cohomology.CoefficientLift.uliftSheafCompose_preservesFiniteLimits.{u, u + 1}
      X.smallEtaleTopology
  have : PreservesFiniteColimits L :=
    Stacks.Cohomology.CoefficientLift.uliftSheafCompose_preservesFiniteColimits.{u, u + 1}
      X.smallEtaleTopology
  let E := Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv.{u, u, u + 1, w}
    X.smallEtaleTopology (additiveSheafBase X) n
  have h1 : Stacks.Cohomology.CoefficientLift.sheafHIsoCongr (additiveSheafBaseUliftIso X).symm n
      (Sheaf.H.map (additiveSheafSmul X a) n x) =
      Sheaf.H.map (L.map (additiveSheafBaseSmul X a)) n
        (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr (additiveSheafBaseUliftIso X).symm n
          x) := by
    change (x.comp (Ext.mk₀ (additiveSheafSmul X a)) (add_zero n)).comp
        (Ext.mk₀ (additiveSheafBaseUliftIso X).inv) (add_zero n) =
      (x.comp (Ext.mk₀ (additiveSheafBaseUliftIso X).inv) (add_zero n)).comp
        (Ext.mk₀ (L.map (additiveSheafBaseSmul X a))) (add_zero n)
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, additiveSheafSmul,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have h2 : ∀ z : Sheaf.H.{u, u} (additiveSheafBase X) n,
      E (Sheaf.H.map (additiveSheafBaseSmul X a) n z) =
        Sheaf.H.map (L.map (additiveSheafBaseSmul X a)) n (E z) := by
    intro z
    have hn := NatTrans.naturality_apply (((extFunctor.{w} n).mapIso
      (Stacks.Cohomology.CoefficientLift.constantSheafUliftIso.{u, u + 1}
        X.smallEtaleTopology).symm.op).inv) (L.map (additiveSheafBaseSmul X a))
      (z.mapExactFunctor L)
    change (((extFunctor.{w} n).mapIso
      (Stacks.Cohomology.CoefficientLift.constantSheafUliftIso.{u, u + 1}
        X.smallEtaleTopology).symm.op).inv.app (L.obj (additiveSheafBase X)))
          ((z.comp (Ext.mk₀ (additiveSheafBaseSmul X a)) (add_zero n)).mapExactFunctor L) =
      ((((extFunctor.{w} n).mapIso
      (Stacks.Cohomology.CoefficientLift.constantSheafUliftIso.{u, u + 1}
        X.smallEtaleTopology).symm.op).inv.app (L.obj (additiveSheafBase X)))
          (z.mapExactFunctor L)).comp (Ext.mk₀ (L.map (additiveSheafBaseSmul X a))) (add_zero n)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    exact hn
  have h2' : E.symm (Sheaf.H.map (L.map (additiveSheafBaseSmul X a)) n
      (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr (additiveSheafBaseUliftIso X).symm n x)) =
      Sheaf.H.map (additiveSheafBaseSmul X a) n (E.symm
        (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr (additiveSheafBaseUliftIso X).symm n
          x)) := by
    rw [AddEquiv.symm_apply_eq, h2, AddEquiv.apply_symm_apply]
  have h3 := ConcreteCategory.congr_hom (additiveSheafBaseHIso_naturality X a n)
    (E.symm
      (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr (additiveSheafBaseUliftIso X).symm n x))
  change (additiveSheafBaseHIso X n).hom (E.symm
      (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr (additiveSheafBaseUliftIso X).symm n
        (Sheaf.H.map (additiveSheafSmul X a) n x))) = _
  rw [h1, h2']
  exact h3

end Lift

/-! ### The Frobenius comparison -/

section Frobenius

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  (k : Type u) [Field k] {X} (f : X ⟶ Spec (.of k))

/-- **`H ^ n (X_étale, 𝐆_a) ≃ H ^ n (X, 𝒪_X)` for a scheme over a field**, the right side the
`k`-vector space `AlgebraicGeometry.cohomologyOverField`. -/
def additiveSheafCohomologyOverFieldEquiv (n : ℕ) :
    Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n ≃+
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n :=
  (additiveSheafHEquiv.{w} X n).trans
    (cohomologyOverFieldAddEquivHgroup k f (SheafOfModules.unit X.ringCatSheaf) n).symm

/-- **The comparison is `k`-linear**: multiplication by the image of `c ∈ k` on `𝐆_a` induces
multiplication by `c` on `H ^ n (X, 𝒪_X)`. -/
theorem additiveSheafCohomologyOverFieldEquiv_smul (c : k) (n : ℕ)
    (x : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n) :
    additiveSheafCohomologyOverFieldEquiv k f n
        (Sheaf.H.map (additiveSheafSmul X (baseScalarSection k f c)) n x) =
      c • additiveSheafCohomologyOverFieldEquiv k f n x := by
  set G := cohomologyOverFieldAddEquivHgroup k f (SheafOfModules.unit X.ringCatSheaf) n
  have h := cohomologyOverFieldAddEquivHgroup_naturality k f
    (globalSmul (baseScalarSection k f c) (SheafOfModules.unit X.ringCatSheaf)) n
    (G.symm (additiveSheafHEquiv.{w} X n x))
  rw [AddEquiv.apply_symm_apply] at h
  change G.symm (additiveSheafHEquiv.{w} X n _) = c • G.symm (additiveSheafHEquiv.{w} X n x)
  rw [additiveSheafHEquiv_smul.{w}]
  exact (G.symm_apply_eq.mpr h.symm).trans (cohomologyOverFieldMap_globalSmul k f c _ n _)

/-- The map induced on cohomology by a difference of morphisms of sheaves. -/
theorem sheafH_map_sub_id {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})] {F : Sheaf J AddCommGrpCat.{u + 1}}
    (φ : F ⟶ F) (n : ℕ) (x : Sheaf.H.{w, u + 1} F n) :
    Sheaf.H.map (φ - 𝟙 F) n x = Sheaf.H.map φ n x - x := by
  have h := Sheaf.H.map_add_apply (φ - 𝟙 F) (𝟙 F) x
  rw [sub_add_cancel, Sheaf.H.map_id_apply] at h
  rw [h, add_sub_cancel_right]

/-- **The top-degree Frobenius comparison, constructed.** For a scheme `X` over a field `k` of
characteristic `p`, in every degree `n` the étale cohomology of `𝐆_a` is identified with
`H ^ n (X, 𝒪_X)` (`additiveSheafCohomologyOverFieldEquiv`), the Frobenius `F` of `H ^ n (X, 𝒪_X)`
is the map induced by the Frobenius `x ↦ x ^ p` of `𝐆_a` transported along it, it is `p`-semilinear
because `(x a) ^ p = x ^ p a ^ p`, and the Artin–Schreier map becomes `F - 1`. -/
@[sga "1 XI 6.8" "partial", sga "7 XXI 1.0", sga "7 XXII 2.0"]
def structureSheafTopDegreeFrobeniusComparison {p : ℕ} (hp : p.Prime) [CharP k p] (n : ℕ) :
    TopDegreeFrobeniusComparison p k f (additiveSheaf.{u, u + 1} X)
      (artinSchreierMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) n where
  equiv := additiveSheafCohomologyOverFieldEquiv k f n
  frobenius := (additiveSheafCohomologyOverFieldEquiv k f n).toAddMonoidHom.comp
    ((Sheaf.H.map (frobeniusMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) n).comp
      (additiveSheafCohomologyOverFieldEquiv k f n).symm.toAddMonoidHom)
  frobenius_smul a v := by
    set E := additiveSheafCohomologyOverFieldEquiv k f n
    have hv : E.symm (a • v) =
        Sheaf.H.map (additiveSheafSmul X (baseScalarSection k f a)) n (E.symm v) := by
      rw [AddEquiv.symm_apply_eq, additiveSheafCohomologyOverFieldEquiv_smul.{w},
        AddEquiv.apply_symm_apply]
    have hpow : baseScalarSection k f (a ^ p) = baseScalarSection k f a ^ p :=
      map_pow _ a p
    simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
    rw [hv, ← Sheaf.H.map_comp_apply, additiveSheafSmul_comp_frobeniusMap,
      Sheaf.H.map_comp_apply, ← hpow, additiveSheafCohomologyOverFieldEquiv_smul.{w}]
  equiv_map x := by
    simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
      AddEquiv.symm_apply_apply]
    rw [artinSchreierMap, sheafH_map_sub_id, map_sub]

end Frobenius

end Stacks.ArtinSchreier

end
