module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedEffaceability.GodementResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.RemainingInterface
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech cohomology is the right derived functor of `Ȟ⁰`: Stacks 01EN

Stacks 01EN says that the Čech cohomology functors `Ȟⁿ(𝒰, -)` on presheaves of `O_X`-modules
are canonically isomorphic, as a δ-functor, to the right derived functors of
`Ȟ⁰(𝒰, -) : PMod(O_X) ⥤ Mod_{O_X(U)}`. `StacksDraft.Ch20.Sec13.Tag01EN` and
`StacksDraft.Ch20.Sec13.Tag01ENFull` prove this modulo three inputs, carried as hypotheses.
Two of them are discharged elsewhere: `EnoughInjectives` on presheaves of modules (Stacks
01DV) by Mathlib's instance `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`, and
effaceability of the Čech δ-functor (Stacks 01EL plus 01EM) by
`Stacks.Cohomology.CechGodement.effaceable_cechDeltaFunctor`. This file builds the third, and
with it the comparison itself.

## The third input

What is still needed is a cohomological δ-functor `G` on presheaves of `R`-modules whose
degree-zero part is degree-zero Čech cohomology and whose components are the right derived
functors of that degree-zero part. Mathlib has no long exact sequence for
`CategoryTheory.Functor.rightDerived`: there is no horseshoe lemma for injective resolutions.
The long exact sequence is instead available for the *derived-category* convention
`CategoryTheory.Functor.rightDerivedPlus`, `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`, through the exactness
of `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`; this file assembles it and then transports it along
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard`, the identification of the
two conventions proved for Stacks 01E4.

The assembly is the one Stacks 05TE asks for. Its input is a δ-functor structure, in the sense
of Stacks 0150, on the composite `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`; here that is obtained by
composing the δ-functor structure of `A ↦ A[0] : 𝒜 ⥤ D⁺(𝒜)` with the exact functor `RF`
(Stacks 0151 (1)). The distinguished triangle of `A ↦ A[0]` is Mathlib's
`ShortComplex.ShortExact.singleTriangle`, pulled back along the fully faithful inclusion
`ι : D⁺(𝒜) ⥤ D(𝒜)`, and `RF` is exact by Stacks 0159.

## Main definitions

* `singlePlusδ`, `singlePlusDeltaFunctorStructure`: the δ-functor structure on
  `A ↦ A[0] : 𝒜 ⥤ D⁺(𝒜)`.
* `derivedDeltaFunctorStructure`: its composite with `RF`, the input of Stacks 05TE.
* `rightDerivedPlusDeltaFunctor`: the cohomological δ-functor `{R ⁱ F}` in the
  `rightDerivedPlus` convention, and `rightDerivedDeltaFunctor` the same one with components
  rewritten as Mathlib's `Functor.rightDerived`.
* `cechRightDerivedDeltaFunctor`: the δ-functor `G` that Stacks 01EN was missing, namely
  `rightDerivedDeltaFunctor` of degree-zero Čech cohomology.

## Main results

* `cechDeltaFunctorIsoRightDerived`: **Stacks 01EN**, the canonical isomorphism of the Čech
  δ-functor with the right-derived δ-functor of its degree-zero part, and
  `cechCohomologyFunctorIsoRightDerived` its degreewise form `Ȟⁿ(𝒰, -) ≅ Rⁿ Ȟ⁰(𝒰, -)`, which
  is the statement Stacks 01EO and 01EP quote from 01EN.
* `cechDeltaFunctorIsoRightDerived_app_zero` and `cechCohomologyFunctorIsoRightDerived_zero`:
  the comparison is the canonical degree-zero identification `Ȟ⁰(𝒰, -) ≅ R⁰ Ȟ⁰(𝒰, -)` in
  degree zero, so it is the normalized one, and is therefore unique by Stacks 010U.

## Implementation notes

`CategoryTheory.Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal` (Stacks 05TE) states
the δ-functor axioms as a nested conjunction of the individual axioms rather than as a
`CategoryTheory.DeltaFunctor`, because its connecting morphism is an argument;
`rightDerivedPlus_deltaAxioms` names that conjunction at the connecting morphism
`rightDerivedPlusδ` built from the δ-functor structure above, and
`rightDerivedPlusDeltaFunctor` packages it. The three exactness axioms arrive as
`∃ hz : _ = 0, _`, the vanishing being needed to state the exactness; the vanishing is a
proposition, so `Exists.choose` and `Exists.choose_spec` split them without any further work.

The commutation of `RF` with the shift and the exactness of `RF` are rebuilt here from
Mathlib's universal property and from Stacks 0159, rather than reused: the versions in
`StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective` are `private`.

Only the first assertion of Stacks 01EN is proved here. The source's *moreover* clause — a
functorial quasi-isomorphism from the Čech complex of a presheaf to the total right derived
functor of `Ȟ⁰`, obtained from the total complex of the Čech complex of an injective
resolution — is not formalized; the source itself marks it as inessential.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
* [Stacks Project, Tag 0150](https://stacks.math.columbia.edu/tag/0150)
* [Stacks Project, Tag 0151](https://stacks.math.columbia.edu/tag/0151)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated TopologicalSpace
open DerivedCategory
open Stacks.Cohomology.CechDerived Stacks.Cohomology.CechEffaceable
open Stacks.Cohomology.CechDerivedFull
open CategoryTheory.Functor (commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit isTriangulated_rightDerivedFunctorPlus)

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.CechDelta

attribute [local instance] HasDerivedCategory.standard

section Abstract

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- **The connecting morphism of the single functor into `D⁺(𝒜)`.** For a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of an abelian category `𝒜`, this is the morphism
`X₃[0] ⟶ (X₁[0])⟦1⟧` of the bounded below derived category whose image under the fully
faithful inclusion `ι : D⁺(𝒜) ⥤ D(𝒜)` is Mathlib's `ShortComplex.ShortExact.singleδ`. -/
def singlePlusδ {S : ShortComplex A} (hS : S.ShortExact) :
    (Plus.singleFunctor A 0).obj S.X₃ ⟶ ((Plus.singleFunctor A 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  Plus.ι.preimage (hS.singleδ ≫
    (Plus.ι.commShiftIso (1 : ℤ)).inv.app ((Plus.singleFunctor A 0).obj S.X₁))

/-- The image of `singlePlusδ` in the full derived category is the connecting morphism
`ShortComplex.ShortExact.singleδ`, read through the commutation of the inclusion
`ι : D⁺(𝒜) ⥤ D(𝒜)` with the shift. This is the defining property of `singlePlusδ`, and all
that is used of it below. -/
lemma ι_map_singlePlusδ {S : ShortComplex A} (hS : S.ShortExact) :
    Plus.ι.map (singlePlusδ hS) ≫
        (Plus.ι.commShiftIso (1 : ℤ)).hom.app ((Plus.singleFunctor A 0).obj S.X₁) =
      hS.singleδ := by
  dsimp only [singlePlusδ]
  rw [Functor.map_preimage]
  exact (Iso.eq_comp_inv ((Plus.ι.commShiftIso (1 : ℤ)).app
    ((Plus.singleFunctor A 0).obj S.X₁))).1 rfl

/-- **The triangle of a short exact sequence is distinguished in `D⁺(𝒜)`.** A triangle of the
bounded below derived category is distinguished exactly when its image under
`ι : D⁺(𝒜) ⥤ D(𝒜)` is, and that image is isomorphic to Mathlib's
`ShortComplex.ShortExact.singleTriangle` by the identification
`DerivedCategory.Plus.singleFunctorιIso` of the two single functors. -/
lemma singlePlusδ_distinguished {S : ShortComplex A} (hS : S.ShortExact) :
    Triangle.mk ((Plus.singleFunctor A 0).map S.f) ((Plus.singleFunctor A 0).map S.g)
      (singlePlusδ hS) ∈ distTriang (Plus A) := by
  rw [← Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _
    (Triangle.isoMk _ _ ((Plus.singleFunctorιIso A 0).app S.X₁)
      ((Plus.singleFunctorιIso A 0).app S.X₂) ((Plus.singleFunctorιIso A 0).app S.X₃)
      ?_ ?_ ?_)
  · exact (Plus.singleFunctorιIso A 0).hom.naturality S.f
  · exact (Plus.singleFunctorιIso A 0).hom.naturality S.g
  · change (Plus.ι.map (singlePlusδ hS) ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁)) ≫
        (shiftFunctor (DerivedCategory A) (1 : ℤ)).map
          (𝟙 ((singleFunctor A 0).obj S.X₁)) =
      𝟙 ((singleFunctor A 0).obj S.X₃) ≫ hS.singleδ
    exact (congrArg (fun v ↦ (Plus.ι.map (singlePlusδ hS) ≫
          (Plus.ι.commShiftIso (1 : ℤ)).hom.app ((Plus.singleFunctor A 0).obj S.X₁)) ≫ v)
        (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory A) (1 : ℤ))
          ((singleFunctor A 0).obj S.X₁))).trans
      ((Category.comp_id _).trans ((ι_map_singlePlusδ hS).trans (Category.id_comp _).symm))

/-- **`singlePlusδ` is natural in the short exact sequence.** The inclusion
`ι : D⁺(𝒜) ⥤ D(𝒜)` is faithful, so it suffices to check the square after applying it and
composing with the commutation of `ι` with the shift; there it is the naturality of
`ShortComplex.ShortExact.singleδ`, which is the third square of the triangle morphism
`ShortComplex.ShortExact.singleTriangle.map`. -/
lemma singlePlusδ_naturality {S₁ S₂ : ShortComplex A} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂) :
    singlePlusδ h₁ ≫ ((Plus.singleFunctor A 0).map φ.τ₁)⟦(1 : ℤ)⟧' =
      (Plus.singleFunctor A 0).map φ.τ₃ ≫ singlePlusδ h₂ := by
  refine Plus.ι.map_injective ((Iso.cancel_iso_hom_right _ _
    ((Plus.ι.commShiftIso (1 : ℤ)).app ((Plus.singleFunctor A 0).obj S₂.X₁))).1 ?_)
  have hnat := (Plus.ι.commShiftIso (1 : ℤ)).hom.naturality ((Plus.singleFunctor A 0).map φ.τ₁)
  have hc := (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ).comm₃
  simp only [ShortComplex.ShortExact.singleTriangle.map_hom₁,
    ShortComplex.ShortExact.singleTriangle.map_hom₃,
    ShortComplex.ShortExact.singleTriangle_mor₃] at hc
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Functor.comp_map] at hnat ⊢
  rw [hnat, ← Category.assoc, ι_map_singlePlusδ h₁, ι_map_singlePlusδ h₂]
  exact hc

/-- **The δ-functor structure of Stacks 0150 on `A ↦ A[0] : 𝒜 ⥤ D⁺(𝒜)`.** The connecting
morphism is `singlePlusδ`, the triangle it completes is distinguished, and it is natural in the
short exact sequence. -/
def singlePlusDeltaFunctorStructure :
    Functor.DeltaFunctorStructure A (Plus A) (Plus.singleFunctor A 0) where
  δ hS := singlePlusδ hS
  distinguished hS := singlePlusδ_distinguished hS
  δ_naturality h₁ h₂ φ := singlePlusδ_naturality h₁ h₂ φ

variable (F : A ⥤ B) [F.Additive] [EnoughInjectives A]

attribute [local instance] commShiftRightDerivedFunctorPlus

attribute [local instance] natTransCommShiftRightDerivedFunctorPlusUnit

attribute [local instance] isTriangulated_rightDerivedFunctorPlus

/-- **The δ-functor structure on `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`**, which is the input Stacks 05TE
asks for: the structure `singlePlusDeltaFunctorStructure` composed with the exact functor `RF`,
as in Stacks 0151 (1). -/
def derivedDeltaFunctorStructure :
    Functor.DeltaFunctorStructure A (Plus B)
      (Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus) :=
  (singlePlusDeltaFunctorStructure (A := A)).comp F.rightDerivedFunctorPlus

/-- **The connecting morphism `R ⁱ F(X₃) ⟶ R ⁱ⁺¹ F(X₁)`** of the higher right derived
functors: the one the long exact homology sequence of `D⁺(ℬ)` attaches to the distinguished
triangle of `derivedDeltaFunctorStructure`. This is the morphism Stacks 05TE prescribes. -/
def rightDerivedPlusδ {S : ShortComplex A} (hS : S.ShortExact) (i : ℕ) :
    (F.rightDerivedPlus i).obj S.X₃ ⟶ (F.rightDerivedPlus (i + 1)).obj S.X₁ :=
  (Plus.homologyFunctor B 0).homologySequenceδ
    (Triangle.mk ((Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus).map S.f)
      ((Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus).map S.g)
      ((derivedDeltaFunctorStructure F).δ hS)) i (i + 1) rfl

/-- **The δ-functor axioms for `{R ⁱ F, rightDerivedPlusδ}`**, Stacks 05TE part (1): each
`R ⁱ F` is additive, `R ⁰ F` preserves the monomorphism of a short exact sequence, and the long
sequence `0 ⟶ R ⁰F(X₁) ⟶ R ⁰F(X₂) ⟶ R ⁰F(X₃) ⟶ R ¹F(X₁) ⟶ ⋯` is exact and natural in the short
exact sequence. -/
lemma rightDerivedPlus_deltaAxioms :
    (∀ i : ℕ, (F.rightDerivedPlus i).Additive) ∧
      (∀ {S : ShortComplex A}, S.ShortExact → Mono ((F.rightDerivedPlus 0).map S.f)) ∧
      (∀ {S : ShortComplex A} (_ : S.ShortExact) (i : ℕ),
        ∃ hz : (F.rightDerivedPlus i).map S.f ≫ (F.rightDerivedPlus i).map S.g = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex A} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : (F.rightDerivedPlus i).map S.g ≫ rightDerivedPlusδ F hS i = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex A} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : rightDerivedPlusδ F hS i ≫ (F.rightDerivedPlus (i + 1)).map S.f = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S S' : ShortComplex A} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') (i : ℕ),
        (F.rightDerivedPlus i).map φ.τ₃ ≫ rightDerivedPlusδ F hS' i =
          rightDerivedPlusδ F hS i ≫ (F.rightDerivedPlus (i + 1)).map φ.τ₁) :=
  (Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal F (derivedDeltaFunctorStructure F)
    (fun hS i ↦ rightDerivedPlusδ F hS i) (fun _ _ ↦ rfl)).1

/-- **The cohomological δ-functor of the higher right derived functors**, in the
derived-category convention `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])` of Stacks 015A. Its components are
`CategoryTheory.Functor.rightDerivedPlus` and its connecting morphism is `rightDerivedPlusδ`;
the axioms are `rightDerivedPlus_deltaAxioms`. -/
def rightDerivedPlusDeltaFunctor : DeltaFunctor A B where
  functor i := F.rightDerivedPlus (i : ℤ)
  additive := (rightDerivedPlus_deltaAxioms F).1
  δ hS i := rightDerivedPlusδ F hS i
  map_g_δ hS i := ((rightDerivedPlus_deltaAxioms F).2.2.2.1 hS i).choose
  δ_map_f hS i := ((rightDerivedPlus_deltaAxioms F).2.2.2.2.1 hS i).choose
  mono_map_f hS := (rightDerivedPlus_deltaAxioms F).2.1 hS
  exact_map hS i := ((rightDerivedPlus_deltaAxioms F).2.2.1 hS i).choose_spec
  exact_δ₁ hS i := ((rightDerivedPlus_deltaAxioms F).2.2.2.1 hS i).choose_spec
  exact_δ₂ hS i := ((rightDerivedPlus_deltaAxioms F).2.2.2.2.1 hS i).choose_spec
  δ_naturality hS hT φ i := (rightDerivedPlus_deltaAxioms F).2.2.2.2.2 hS hT φ i

/-- **Isomorphic additive functors have isomorphic right derived functors.** Mathlib's
`NatTrans.rightDerived` is functorial in the natural transformation, so it carries an
isomorphism to an isomorphism. -/
def rightDerivedIsoOfIso {F₁ F₂ : A ⥤ B} [F₁.Additive] [F₂.Additive] (e : F₁ ≅ F₂) (n : ℕ) :
    F₁.rightDerived n ≅ F₂.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- **The cohomological δ-functor whose components are Mathlib's right derived functors.** It
is `rightDerivedPlusDeltaFunctor` transported along the identification
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard` of the derived-category and
injective-resolution conventions for `R ⁱ F`. This is the δ-functor that Stacks 01EN needs and
that Mathlib does not provide: `CategoryTheory.Functor.rightDerived` has no long exact sequence
of its own. -/
@[ega "0 12.2.1" "partial"]
def rightDerivedDeltaFunctor : DeltaFunctor A B :=
  (rightDerivedPlusDeltaFunctor F).ofIso (fun n ↦ F.rightDerived n)
    fun n ↦ Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard F n

/-- The component functors of `rightDerivedDeltaFunctor` are the right derived functors of `F`
on the nose. -/
lemma rightDerivedDeltaFunctor_functor (n : ℕ) :
    (rightDerivedDeltaFunctor F).functor n = F.rightDerived n :=
  rfl

end Abstract

section Cech

variable {Y : TopCat.{0}} (R : (Opens Y)ᵒᵖ ⥤ RingCat.{0}) (𝒰 : CechOpenCover Y)

/-- **The third input of Stacks 01EN.** The cohomological δ-functor on presheaves of
`R`-modules whose components are the right derived functors of degree-zero Čech cohomology of
the covering `𝒰`, with the connecting morphisms of the long exact sequence of `D⁺`. -/
def cechRightDerivedDeltaFunctor : DeltaFunctor (Modules R) (SectionModules R 𝒰) :=
  rightDerivedDeltaFunctor (cechCohomologyFunctor R 𝒰 0)

/-- The component functors of `cechRightDerivedDeltaFunctor` are, on the nose, the right
derived functors of degree-zero Čech cohomology. This is what makes it the target Stacks 01EN
asks for, and the content of `cechDeltaFunctorIsoRightDerived`. -/
lemma cechRightDerivedDeltaFunctor_functor (n : ℕ) :
    (cechRightDerivedDeltaFunctor R 𝒰).functor n = (cechCohomologyFunctor R 𝒰 0).rightDerived n :=
  rfl

/-- **The degree-zero input of Stacks 01EN.** Degree-zero Čech cohomology is left exact, hence
canonically its own zeroth right derived functor, which is the degree-zero component of
`cechRightDerivedDeltaFunctor`; the comparison is inverse to
`CategoryTheory.Functor.toRightDerivedZero`. -/
def cechRightDerivedZeroIso :
    cechCohomologyFunctor R 𝒰 0 ≅ (cechRightDerivedDeltaFunctor R 𝒰).functor 0 :=
  (cechIsoRightDerivedZero R 𝒰).symm

/-- **The positive-degree input of Stacks 01EN.** The degree-`n+1` component of
`cechRightDerivedDeltaFunctor` is the `(n+1)`-st right derived functor of its own degree-zero
component: the two differ only by the canonical identification of degree-zero Čech cohomology
with its zeroth right derived functor, which `rightDerivedIsoOfIso` propagates to every
degree. -/
def cechRightDerivedSuccIso (n : ℕ) :
    (cechRightDerivedDeltaFunctor R 𝒰).functor (n + 1) ≅
      ((cechRightDerivedDeltaFunctor R 𝒰).functor 0).rightDerived (n + 1) :=
  letI : ((cechCohomologyFunctor R 𝒰 0).rightDerived 0).Additive :=
    Functor.additive_of_iso (Functor.rightDerivedZeroIsoSelf (cechCohomologyFunctor R 𝒰 0)).symm
  (rightDerivedIsoOfIso (Functor.rightDerivedZeroIsoSelf (cechCohomologyFunctor R 𝒰 0))
    (n + 1)).symm

/-- **Stacks 01EN, first assertion.** Čech cohomology of the covering `𝒰`, as the cohomological
δ-functor on presheaves of `R`-modules of Stacks 01EK, is canonically isomorphic to the
right-derived δ-functor of its degree-zero part. All three inputs of Stacks 01EN are now
available: enough injectives on presheaves of modules (Stacks 01DV), effaceability of the Čech
δ-functor (Stacks 01EL and 01EM), and the δ-functor `cechRightDerivedDeltaFunctor` realizing
the right derived functors. The argument is the one of Stacks 010T and 010U: both δ-functors
are universal, and universal δ-functors with the same degree-zero part are uniquely
isomorphic. -/
@[stacks 01EN "the canonical delta-functor isomorphism"]
def cechDeltaFunctorIsoRightDerived : cechDeltaFunctor R 𝒰 ≅ cechRightDerivedDeltaFunctor R 𝒰 :=
  cechDeltaIsoRightDerivedOfIso₀ R 𝒰 (cechRightDerivedDeltaFunctor R 𝒰)
    (cechRightDerivedZeroIso R 𝒰) (cechRightDerivedSuccIso R 𝒰)

/-- The comparison of Stacks 01EN induces the canonical degree-zero identification in degree
zero; this is the normalization that makes it the unique such isomorphism, by Stacks 010U. -/
theorem cechDeltaFunctorIsoRightDerived_app_zero :
    (cechDeltaFunctorIsoRightDerived R 𝒰).hom.app 0 = (cechRightDerivedZeroIso R 𝒰).hom :=
  cechDeltaIsoRightDerivedOfIso_app_zero R 𝒰 (cechRightDerivedDeltaFunctor R 𝒰)
    (cechRightDerivedZeroIso R 𝒰) (cechRightDerivedSuccIso R 𝒰)

/-- **Stacks 01EN, degreewise.** Degree-`n` Čech cohomology of the covering `𝒰` on presheaves
of `R`-modules is canonically isomorphic to the `n`-th right derived functor of degree-zero
Čech cohomology: `Ȟⁿ(𝒰, -) = Rⁿ Ȟ⁰(𝒰, -)`. This is the identification that Stacks 01EO and
01EP quote from 01EN; it is the degree-`n` component of
`cechDeltaFunctorIsoRightDerived`. -/
def cechCohomologyFunctorIsoRightDerived (n : ℕ) :
    cechCohomologyFunctor R 𝒰 n ≅ (cechCohomologyFunctor R 𝒰 0).rightDerived n :=
  CategoryTheory.DeltaFunctor.appIso (cechDeltaFunctorIsoRightDerived R 𝒰) n

/-- In degree zero the degreewise comparison of Stacks 01EN is the canonical identification of
degree-zero Čech cohomology with its own zeroth right derived functor. -/
theorem cechCohomologyFunctorIsoRightDerived_zero :
    cechCohomologyFunctorIsoRightDerived R 𝒰 0 = (cechIsoRightDerivedZero R 𝒰).symm :=
  Iso.ext (cechDeltaFunctorIsoRightDerived_app_zero R 𝒰)

end Cech

end Stacks.Cohomology.CechDelta

end
