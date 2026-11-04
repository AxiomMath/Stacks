module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageDegreeZeroColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageIsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImagePresentedInjectiveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentationAdjointForm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0EYM: the colimit assertion `R^p g_* 𝓕 = colim h_i^{-1} R^p g_{i, *}F_i`

Let `I` be a directed set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes
over `I` with affine transition morphisms, let `g_i : X_i ⟶ S_i` be a morphism of the first into
the second with every `g_i` quasi-compact and quasi-separated, let `X = lim X_i`, `S = lim S_i` and
`g : X ⟶ S` the limit morphism. Let `(F_i, φ_{i'i})` be a system of abelian sheaves on
`(X_i, f_{i'i})` and `𝓕 = colim f_i^{-1}F_i`. Then for every `p ≥ 0`

`R^p g_* 𝓕 = colim_i h_i^{-1} R^p g_{i, *}F_i`,

the colimit being along the maps `ψ_{i'i}` and with the cocone maps `ψ_i` of
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` and
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap`, in the universal-property form
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsHigherDirectImageColimit`.

By the dimension shift
`LimitHigherDirectImage.isHigherDirectImageColimit_of_degreeZero_of_vanishing` (which runs on
[Stacks, Tag 0EXZ] and the long exact sequences of the higher direct images and of the base change
maps) it suffices to treat `p = 0` and to show that `R^p g_* 𝓕 = 0` for `p > 0` when every `F_i`
is injective. The latter is
`LimitHigherDirectImage.isZero_rightDerived_limitMorphism_of_injective_presentedSystem`
([Stacks, Tag 09YQ] over the base changes `U_i ×_{S_i} X_i` of affine étale `S_i`-schemes). The
former is `Stacks.EtaleCohomology.LimitHigherDirectImage.existsUnique_directImage_desc` (the
colimit of sections of [Stacks, Tag 09YQ] over quasi-compact quasi-separated objects, and the
colimit half of [Stacks, Tag 0EYN] on `S`), read through `R^0 g_* = g_*` and the description of
the base change map on higher direct images in degree zero
(`Colimits/LimitHigherDirectImageIsColimit.lean`).

## Main results

* `LimitHigherDirectImage.isHigherDirectImageColimit_zero_of_presentedSystem`: the colimit
  assertion in degree zero, for a presented system.
* `LimitHigherDirectImage.isHigherDirectImageColimit_of_isLimit`: the colimit assertion
  `R^p g_* 𝓕 = colim_i h_i^{-1} R^p g_{i, *}F_i` in every degree `p`.

## Implementation notes

The schemes are in `Scheme.{max u v}` for an index `I : Type v`: this is the universe arrangement
of the development's [Stacks, Tag 09YQ], and for `v ≤ u` it is `Scheme.{u}`.

The hypotheses on families indexed by pairs of indices are stated with strict-implicit binders
`⦃i j⦄`: the compatibility hypotheses are passed on whole, and with ordinary implicit binders the
elaborator would instantiate them with metavariables and unify the instantiated statements again.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology Stacks.EtaleCohomology.LimitDirectImage

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

/-- The cancellation behind the compatibility of the transposed family in degree zero, on
variables in a single category. -/
private theorem compat_algebra {C : Type*} [Category* C] {A A' B B' B'' B₂ G : C}
    {f₁ : A ⟶ B} {m : B ⟶ B'} {n : B' ⟶ B''} {t : B'' ⟶ G} {p : A ⟶ A'} {q : A' ⟶ B₂}
    {r : B ⟶ B₂} {s : B₂ ⟶ B''} {t' : A' ⟶ G} (h₁ : m ≫ n = r ≫ s) (h₂ : p ≫ q = f₁ ≫ r)
    (h₃ : q ≫ s ≫ t = t') : f₁ ≫ m ≫ n ≫ t = p ≫ t' := by
  rw [← h₃, ← Category.assoc p, h₂, Category.assoc, ← reassoc_of% h₁]

section Main

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {DX DS : Iᵒᵖ ⥤ Scheme.{max u v}} (γ : DX ⟶ DS) {cX : Cone DX} (hcX : IsLimit cX)
  (cS : Cone DS) (hcS : IsLimit cS)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)]

/-- The compatibility of a family out of the `h_i^{-1} R^0 g_{i, *}F_i` with the transition maps
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` in degree zero: the hypothesis of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsHigherDirectImageColimit` at `p = 0`. -/
def IsZeroCompatible (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtaleRightDerivedZero (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢) : Prop :=
  ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
    (conePullbackComp cS a).inv.app ((smallEtaleRightDerivedZero (γ.app j)).obj (E.sys.obj j)) ≫
      (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ 0 E.sys a) ≫ τ i = τ j

/-- The family `h_i^{-1} g_{i, *}F_i ⟶ 𝒢` induced by a family out of the
`h_i^{-1} R^0 g_{i, *}F_i` through `R^0 g_{i, *} = g_{i, *}`. -/
def zeroFamily (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtaleRightDerivedZero (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢) (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtalePushforwardAb (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢 :=
  (smallEtalePullbackAb (cS.π.app i)).map
    ((smallEtaleRightDerivedZeroIso (γ.app i)).hom.app (E.sys.obj i)) ≫ τ i

/-- The compatibility of a family of maps out of the `h_i^{-1} g_{i, *}F_i` with the degree-zero
transition maps of the direct images. -/
def IsPullbackCompatible (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (x : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtalePushforwardAb (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢) : Prop :=
  ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
    (conePullbackComp cS a).inv.app (directImage γ AddCommGrpCat.{max u v + 1} E.sys j) ≫
      (smallEtalePullbackAb (cS.π.app i)).map
        (LimitDirectImage.transitionMap γ AddCommGrpCat.{max u v + 1} E.sys a) ≫ x i = x j

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)] in
/-- The compatibility of a family out of the `h_i^{-1} R^0 g_{i, *}F_i`, read on the family out of
the `h_i^{-1} g_{i, *}F_i` it induces through `R^0 g_{i, *} = g_{i, *}`. -/
theorem zeroTranspose_key (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtaleRightDerivedZero (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢)
    (hτ : IsZeroCompatible γ cS E τ) :
    IsPullbackCompatible γ cS E (zeroFamily γ cS E τ) := by
  intro i j a
  unfold zeroFamily
  refine compat_algebra (r := (systemPullback DS AddCommGrpCat.{max u v + 1} a ⋙
      smallEtalePullbackAb (cS.π.app i)).map
        ((smallEtaleRightDerivedZeroIso (γ.app j)).hom.app (E.sys.obj j))) ?_ ?_ (hτ a)
  · exact ((smallEtalePullbackAb (cS.π.app i)).map_comp _ _).symm.trans
      ((congrArg (smallEtalePullbackAb (cS.π.app i)).map
        (transitionMap_ab_comp_rightDerivedZeroIso γ E.sys a)).trans
        ((smallEtalePullbackAb (cS.π.app i)).map_comp _ _))
  · exact (conePullbackComp cS a).inv.naturality
      ((smallEtaleRightDerivedZeroIso (γ.app j)).hom.app (E.sys.obj j))

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)] in
/-- **A family out of the `h_i^{-1} g_{i, *}F_i` compatible with the degree-zero transition maps
transposes to a compatible family of maps of direct images.** -/
theorem isDirectImageFamily_homEquiv (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (x : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtalePushforwardAb (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢)
    (hx : IsPullbackCompatible γ cS E x) :
    IsDirectImageFamily γ cS E (fun i => (smallEtaleAdjunctionAb (cS.π.app i)).homEquiv
      ((smallEtalePushforwardAb (γ.app i)).obj (E.sys.obj i)) 𝒢 (x i)) := by
  intro i j a
  apply ((smallEtaleAdjunctionAb (cS.π.app j)).homEquiv
    ((smallEtalePushforwardAb (γ.app j)).obj (E.sys.obj j)) 𝒢).symm.injective
  refine Eq.trans ?_ (leftAdjointCompIso_inv_homEquiv_symm
    (systemAdjunction DS AddCommGrpCat.{max u v + 1} a) (smallEtaleAdjunctionAb (cS.π.app i))
    (smallEtaleAdjunctionAb (cS.π.app j)) (coneDirectImageCompAb cS a)
    (directTransition γ AddCommGrpCat.{max u v + 1} E.sys a)
    ((smallEtaleAdjunctionAb (cS.π.app i)).homEquiv
      ((smallEtalePushforwardAb (γ.app i)).obj (E.sys.obj i)) 𝒢 (x i)))
  have htm : ((systemAdjunction DS AddCommGrpCat.{max u v + 1} a).homEquiv _ _).symm
      (directTransition γ AddCommGrpCat.{max u v + 1} E.sys a) =
        LimitDirectImage.transitionMap γ AddCommGrpCat.{max u v + 1} E.sys a :=
    (congrArg ((systemAdjunction DS AddCommGrpCat.{max u v + 1} a).homEquiv _ _).symm
      (directTransition_eq γ AddCommGrpCat.{max u v + 1} E.sys a)).trans
        (Equiv.symm_apply_apply _ _)
  refine ((Equiv.symm_apply_apply _ _).trans (hx a).symm).trans ?_
  refine congrArg ((conePullbackComp cS a).inv.app
    (directImage γ AddCommGrpCat.{max u v + 1} E.sys j) ≫ ·) ?_
  exact congrArg₂ (fun m n => (smallEtalePullbackAb (cS.π.app i)).map m ≫ n) htm.symm
    (Equiv.symm_apply_apply _ _).symm

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)] in
/-- The transposed family of `Stacks.EtaleCohomology.LimitHigherDirectImage.zeroFamily` is
compatible with the transition maps of the direct images. -/
theorem isDirectImageFamily_zeroFamily (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtaleRightDerivedZero (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢)
    (hτ : IsZeroCompatible γ cS E τ) :
    IsDirectImageFamily γ cS E (fun i => (smallEtaleAdjunctionAb (cS.π.app i)).homEquiv
      ((smallEtalePushforwardAb (γ.app i)).obj (E.sys.obj i)) 𝒢 (zeroFamily γ cS E τ i)) :=
  isDirectImageFamily_homEquiv γ cS E (zeroFamily γ cS E τ) (zeroTranspose_key γ cS E τ hτ)

include hcX in
/-- `Stacks.EtaleCohomology.LimitHigherDirectImage.existsUnique_directImage_desc` with the direct
images written as `Stacks.EtaleCohomology.smallEtalePushforwardAb`. -/
theorem existsUnique_directImage_desc_ab (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    {σ : ∀ i : Iᵒᵖ, directImage γ AddCommGrpCat.{max u v + 1} E.sys i ⟶
      (smallEtalePushforward (cS.π.app i) AddCommGrpCat.{max u v + 1}).obj 𝒢}
    (hσ : IsDirectImageFamily γ cS E σ) :
    ∃! χ : (smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).obj E.sheaf ⟶ 𝒢,
      ∀ i : Iᵒᵖ, legProjection γ cS hcS E i ≫
        (smallEtalePushforwardAb (cS.π.app i)).map χ = σ i :=
  existsUnique_directImage_desc γ hcX cS hcS E hσ

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)] in
/-- The factorisation condition of the colimit assertion in degree zero, for a presented system,
read on the transposed cocone maps
`Stacks.EtaleCohomology.LimitHigherDirectImage.legProjection`. -/
theorem projectionMap_zero_comp_iff_legProjection
    (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtaleRightDerivedZero (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢) (i : Iᵒᵖ)
    (y : (smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).obj E.sheaf ⟶ 𝒢) :
    projectionMap γ cX cS hcS 0 E.sheaf E.sys (transportLeg E.sys E.sheaf E.ι) i ≫
          ((smallEtaleRightDerivedZeroIso (limitMorphism γ cX cS hcS)).inv.app E.sheaf ≫ y :
            (smallEtaleRightDerivedZero (limitMorphism γ cX cS hcS)).obj E.sheaf ⟶ 𝒢) =
        τ i ↔
      legProjection γ cS hcS E i ≫ (smallEtalePushforwardAb (cS.π.app i)).map y =
        (smallEtaleAdjunctionAb (cS.π.app i)).homEquiv
          ((smallEtalePushforwardAb (γ.app i)).obj (E.sys.obj i)) 𝒢 (zeroFamily γ cS E τ i) := by
  unfold zeroFamily
  exact projectionMap_zero_comp_iff γ cX cS hcS E.sheaf E.sys (transportLeg E.sys E.sheaf E.ι) i
    (τ i) y

include hcX in
/-- The universal property of [Stacks, Tag 0EYM] in degree zero, for a family `τ` out of the
`h_i^{-1} R^0 g_{i, *}F_i` compatible with the transition maps. -/
theorem existsUnique_projectionMap_zero (E : PresentedSystem (c := cX) IsColimitPresentation)
    {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{max u v + 1}}
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtaleRightDerivedZero (γ.app i)).obj (E.sys.obj i)) ⟶ 𝒢)
    (hτ : IsZeroCompatible γ cS E τ) :
    ∃! χ : (smallEtaleRightDerivedZero (limitMorphism γ cX cS hcS)).obj E.sheaf ⟶ 𝒢,
      ∀ i : Iᵒᵖ, projectionMap γ cX cS hcS 0 E.sheaf E.sys (transportLeg E.sys E.sheaf E.ι) i ≫
        χ = τ i := by
  obtain ⟨χ', hχ', hu⟩ := existsUnique_directImage_desc_ab γ hcX cS hcS E
    (isDirectImageFamily_zeroFamily γ cS E τ hτ)
  refine ⟨_, fun i => (projectionMap_zero_comp_iff_legProjection γ cS hcS E τ i χ').mpr (hχ' i),
    fun χ hχ => ?_⟩
  have e := Iso.inv_hom_id_app_assoc (smallEtaleRightDerivedZeroIso (limitMorphism γ cX cS hcS))
    E.sheaf χ
  have h₁ : (smallEtaleRightDerivedZeroIso (limitMorphism γ cX cS hcS)).hom.app E.sheaf ≫ χ =
      χ' :=
    hu _ fun i => (projectionMap_zero_comp_iff_legProjection γ cS hcS E τ i _).mp
      (by rw [e]; exact hχ i)
  exact h₁ ▸ e.symm

include hcX in
/-- **[Stacks, Tag 0EYM] in degree zero.** For a presented system `𝓕 = colim f_i^{-1}F_i` the
direct image `R^0 g_* 𝓕` is the colimit of the `h_i^{-1} R^0 g_{i, *}F_i` along the maps of
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap`, with the cocone maps of
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap`. -/
theorem isHigherDirectImageColimit_zero_of_presentedSystem
    (E : PresentedSystem (c := cX) IsColimitPresentation) :
    IsHigherDirectImageColimit γ 0 cX cS hcS E.sheaf E.sys (transportLeg E.sys E.sheaf E.ι) := by
  intro 𝒢 τ hτ
  have h₁ : IsZeroCompatible γ cS E τ := fun i j a => by convert hτ a using 3
  exact existsUnique_projectionMap_zero γ hcX cS hcS E τ h₁

include hcX in
/-- Let `I` be a directed set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of
schemes over `I` with affine transition morphisms, let `g_i : X_i ⟶ S_i` be a morphism of inverse
systems with every `g_i` quasi-compact and quasi-separated, let `X = lim X_i`, `S = lim S_i` and
`g : X ⟶ S` the limit morphism. Let `(F_i, φ_{i'i})` be a system of abelian
sheaves on `(X_i, f_{i'i})` and `ι_i : f_i^{-1}F_i ⟶ 𝓕` maps, compatible with the transition maps,
presenting `𝓕 = colim f_i^{-1}F_i`. Then for every `p ≥ 0`

`R^p g_* 𝓕 = colim_{i ∈ I} h_i^{-1} R^p g_{i, *}F_i`:

every family of maps out of the `h_i^{-1} R^p g_{i, *}F_i` compatible with the maps
`h_{i'}^{-1}ψ_{i'i}` induced by the transition maps
`ψ_{i'i} : h_{i'i}^{-1} R^p g_{i, *}F_i ⟶ R^p g_{i', *}F_{i'}` factors uniquely through the cocone
maps `ψ_i : h_i^{-1} R^p g_{i, *}F_i ⟶ R^p g_* 𝓕`, both families being built from the base change
maps on higher direct images as in the source
(`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap`,
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap`). -/
@[stacks 0EYM, sga "4 VII 5.11" "more general"]
theorem isHigherDirectImageColimit_of_isLimit (p : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{max u v + 1})
    (F : EtaleSheafSystem DX Ab.{max u v + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp cX a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (cX.π.app i)).map (F.map a) ≫ ι i = ι j)
    (hpres : IsPullbackColimitPresentation cX 𝓕 F ι) :
    IsHigherDirectImageColimit γ p cX cS hcS 𝓕 F ι := by
  have h' : transportLeg F 𝓕 (untransportLeg F 𝓕 ι) = ι :=
    funext (transportLeg_untransportLeg F 𝓕 ι)
  have hc : IsColimitPresentation F 𝓕 (untransportLeg F 𝓕 ι) := by
    refine (isColimitPresentation_iff F 𝓕 _).mpr
      ⟨(isCompatibleFamily_iff F 𝓕 _).mpr fun a => ?_, ?_⟩ <;> rw [h']
    exacts [hι a, hpres]
  have h := isHigherDirectImageColimit_of_degreeZero_of_vanishing γ cX cS hcS
    (fun E => isHigherDirectImageColimit_zero_of_presentedSystem γ hcX cS hcS E)
    (fun E hinj q =>
      isZero_rightDerived_limitMorphism_of_injective_presentedSystem γ cX cS hcS hcX E hinj q) p
    (presentedSystemOfIsColimitPresentation F 𝓕 _ hc)
  rw [← h']
  exact h

end Main

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
