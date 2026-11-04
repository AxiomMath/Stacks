/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.TwistedDoubleFormalScheme

/-!
# The twisted double has no fundamental system of cut-out ideals of definition

The twisted double `AlgebraicGeometry.TwistedDouble.D` is two copies of `Y = Spf R⟦X⟧` glued
along `W = ⨆ pt n` by the substitutions `X ↦ X - ε n` over `pt n`. We show that it has no
fundamental system of ideals of definition cut out by their sections over the affine formal opens.
Hence, by `AlgebraicGeometry.FormalScheme.isFppfColimitOfThickenings_iff`, its functor of points
is not a colimit of schemes along thickenings.

Let `p` be the point at `(X)` of the copy `true`. Its kernel over `U true` is open, so a
fundamental system contains a member `J` whose sections over `U true` are killed by `p`. The
sections of `J` over `U false` form an open ideal, so they contain the section `sec M` attached to
`X ^ M` through the chart of the copy `false`, for some `M`. In the chart of the copy `true`,
the restriction of `sec M` to the point `η n` is `(X - ε n) ^ M`
(`AlgebraicGeometry.TwistedDouble.h_true_c_app_res_sec`). For `n ≥ M`, `p` does not kill it,
because `ε n ^ M ≠ 0` in `R_{y n}`. But the cut-out condition at `U true` forces `p` to kill
every section of `J` over an open inside `U true`.

## Main results

* The abstract obstruction, for any class of opens:
  `LocallyTopologicallyRingedSpace.not_exists_isCutOutOn_isFundamentalSystemOfIdealsOfDefinitionOn`
* `AlgebraicGeometry.TwistedDouble.h_true_c_app_res_sec`: the twist computation.
* `AlgebraicGeometry.TwistedDouble.not_exists_isCutOutOn_isFundamentalSystemOfIdealsOfDefinitionOn`
  and `AlgebraicGeometry.TwistedDouble.not_isFppfColimitOfThickenings`.

## Implementation notes

The twist is evaluated through the open immersion `k n` of `pt n` into `Y`. Its components over
the opens inside `pt n` are isomorphisms, and `k n ≫ h true = k n ≫ σ n ≫ h false`
(`AlgebraicGeometry.TwistedDouble.k_comp_h_true`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In a presheaf on a space, two successive restrictions are the restriction along any arrow with
the same endpoints: arrows between opens are unique. -/
theorem TopCat.Presheaf.map_map_apply_of_subsingleton {Z : TopCat.{u}}
    (F : Z.Presheaf TopCommRingCat.{u}) {U V W : Opens Z} (f : op U ⟶ op V) (g : op V ⟶ op W)
    (i : op U ⟶ op W) (x : (F.obj (op U)).α) :
    (F.map g).1 ((F.map f).1 x) = (F.map i).1 x := by
  rw [show i = f ≫ g from Quiver.Hom.unop_inj (Subsingleton.elim _ _), F.map_comp]
  rfl

/-- Equal morphisms of presheafed spaces have the same components, in the form: if `β` sends `x`
over `V` to the restriction of a global section `y`, so does `α = β`. -/
theorem PresheafedSpace.c_app_apply_eq_of_eq {X Y : PresheafedSpace TopCommRingCat.{u}}
    {α β : X ⟶ Y} (h : α = β) (V : Opens Y) (x : (Y.presheaf.obj (op V)).α)
    (y : (X.presheaf.obj (op ⊤)).α)
    (hβ : (β.c.app (op V)).1 x = (X.presheaf.map (homOfLE le_top).op).1 y) :
    (α.c.app (op V)).1 x = (X.presheaf.map (homOfLE le_top).op).1 y := by
  subst h
  exact hβ

/-- The components of a morphism of presheafed spaces commute with restriction, elementwise. -/
theorem PresheafedSpace.c_app_map_homOfLE_apply {X Y : PresheafedSpace TopCommRingCat.{u}}
    (f : X ⟶ Y) {V W : Opens Y} (hVW : V ≤ W) (x : (Y.presheaf.obj (op W)).α) :
    (f.c.app (op V)).1 ((Y.presheaf.map (homOfLE hVW).op).1 x) =
      (X.presheaf.map (homOfLE ((Opens.map f.base).monotone hVW)).op).1 ((f.c.app (op W)).1 x) :=
  congrArg (fun φ => φ.1 x) (f.c.naturality (homOfLE hVW).op)

section ChartSection

open LocallyTopologicallyRingedSpace

variable {X : LTRS.{u}} {U : Opens X} {A : TopCommRingCat.{u}}
  (hA : TopologicalRing.IsPreAdmissible A.α)
  (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A.α)

/-- The sections of `𝒪_X` over the open `U` of an affine formal chart `X|_U ≅ Spf A` attached to
the elements of `A`: the inverse of the chart on sections over `U`, after `A → Γ(Spf A)`. -/
noncomputable def spfChartSection : TopCommRingCat.of A.α ⟶ X.presheaf.obj (op U) :=
  spfGammaHom A.α ≫ (spfLTRS A.α hA).presheaf.map (homOfLE le_top).op ≫
    inv (I := isIso_spfChartHom_c_app hA e (le_refl U)) ((spfChartHom hA e).toHom.c.app (op U))

/-- The chart sends the section attached to `a` to the restriction of `a`. -/
theorem spfChartHom_c_app_spfChartSection (a : A.α) :
    ((spfChartHom hA e).toHom.c.app (op U)).1 ((spfChartSection hA e).1 a) =
      ((spfLTRS A.α hA).presheaf.map (homOfLE le_top).op).1 ((spfGammaHom A.α).1 a) :=
  congrArg (fun g => g.1 (((spfLTRS A.α hA).presheaf.map (homOfLE le_top).op).1
      ((spfGammaHom A.α).1 a)))
    (IsIso.inv_hom_id (I := isIso_spfChartHom_c_app hA e (le_refl U))
      ((spfChartHom hA e).toHom.c.app (op U)))

/-- The chart sends the restriction of the section attached to `a` to an open inside the chart to
the restriction of `a`. -/
theorem spfChartHom_c_app_res_spfChartSection {V : Opens X} (hV : V ≤ U) (a : A.α) :
    ((spfChartHom hA e).toHom.c.app (op V)).1 ((X.presheaf.map (homOfLE hV).op).1
      ((spfChartSection hA e).1 a)) =
      ((spfLTRS A.α hA).presheaf.map (homOfLE le_top).op).1 ((spfGammaHom A.α).1 a) := by
  rw [PresheafedSpace.c_app_map_homOfLE_apply, spfChartHom_c_app_spfChartSection]
  exact TopCat.Presheaf.map_map_apply_of_subsingleton _ _ _ _ _

end ChartSection

namespace LocallyTopologicallyRingedSpace

/-- **An obstruction to a fundamental system of cut-out ideals of definition.** Let `U₀` and `U₁`
be opens of a class `𝒜`, and `p : T ⟶ X` a point of `X` by a scheme, landing in `U₀`, whose kernel
over `U₀` is a neighbourhood of zero. If every open ideal of `𝒪_X(U₁)` has an element whose
restriction to some open `η` inside `U₀ ∩ U₁` is not killed by `p`, then no fundamental system of
ideals of definition on `𝒜` consists of ideal sheaves cut out by their sections over `𝒜`. -/
theorem not_exists_isCutOutOn_isFundamentalSystemOfIdealsOfDefinitionOn {X : LTRS.{u}}
    {𝒜 : Opens X → Prop} {U₀ U₁ : Opens X} (hU₀ : 𝒜 U₀) (hU₁ : 𝒜 U₁) {T : Scheme.{u}}
    (p : schemeToLTRSObj T ⟶ X) (hp : Set.range p.toHom.base ⊆ (U₀ : Set X))
    (hker : ((IdealSheaf.ker p).ideal U₀ : Set (X.presheaf.obj (op U₀)).α) ∈ nhds 0)
    (ht : ∀ L : Ideal (X.presheaf.obj (op U₁)).α, IsOpen (L : Set (X.presheaf.obj (op U₁)).α) →
      ∃ (η : Opens X) (_ : η ≤ U₀) (hη₁ : η ≤ U₁), ∃ t ∈ L,
        (p.toHom.c.app (op η)).1 ((X.presheaf.map (homOfLE hη₁).op).1 t) ≠ 0) :
    ¬ ∃ 𝒮 : Set (IdealSheaf X), (∀ I ∈ 𝒮, I.IsCutOutOn 𝒜) ∧
        IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 𝒜 := by
  rintro ⟨𝒮, hC, hfund⟩
  obtain ⟨J, hJ, hJU⟩ := (hfund.2 U₀ hU₀).mem_iff.mp hker
  obtain ⟨η, hη₀, hη₁, t, htL, htne⟩ := ht (J.ideal U₁) (hfund.1 J hJ U₁ hU₁).1
  have hres : (X.presheaf.map (homOfLE hη₁).op).1 t ∈ J.ideal η := J.map_mem hη₁ htL
  exact htne (((hC J hJ) U₀ hU₀ η hη₀ _).mp hres T p hp fun s hs =>
    IdealSheaf.mem_ker_iff.mp (hJU hs))

end LocallyTopologicallyRingedSpace

namespace TwistedDouble

open LocallyTopologicallyRingedSpace PowerSeriesFormalSpectrum

open PowerSeries (X C)

/-- A morphism of topological rings which is an isomorphism is injective. -/
theorem _root_.TopCommRingCat.injective_of_isIso {B B' : TopCommRingCat.{u}} (f : B ⟶ B')
    [IsIso f] : Function.Injective f.1 :=
  (ConcreteCategory.bijective_of_isIso f).1

/-- The section of `𝒪_D` over the copy `U false` attached to `X ^ M`. -/
noncomputable def sec (M : ℕ) : (D.presheaf.obj (op (U false))).α :=
  (spfChartSection (isPreAdmissible BouquetRing.R) (e false)).1 (X ^ M)

/-- The copy `false` sends the restriction of `sec M` to the restriction of `X ^ M`. -/
theorem h_false_c_app_res_sec {V : Opens D} (hV : V ≤ U false) (M : ℕ) :
    ((h false).toHom.c.app (op V)).1 ((D.presheaf.map (homOfLE hV).op).1 (sec M)) =
      (Y.presheaf.map (homOfLE le_top).op).1 ((spfGammaHom A.α).1 (X ^ M)) :=
  spfChartHom_c_app_res_spfChartSection _ _ hV _

/-- The automorphism `σ n` sends the restriction of `a` to the restriction of `a(X - ε n)`. -/
theorem σ_c_app_res (n : ℕ) (V : Opens Y) (a : A.α) :
    ((σ n).hom.toHom.c.app (op V)).1 ((Y.presheaf.map (homOfLE le_top).op).1
      ((spfGammaHom A.α).1 a)) =
      (Y.presheaf.map (homOfLE le_top).op).1
        ((spfGammaHom A.α).1 (subst (BouquetRing.ε n) (isNilpotent_ε n) a)) :=
  aut_hom_c_app_res _ _ V a

/-- The substitution `X ↦ X - ε n` sends `X ^ M` to `(X - ε n) ^ M`. -/
theorem subst_X_pow (n M : ℕ) :
    subst (BouquetRing.ε n) (isNilpotent_ε n) (X ^ M : A.α) = (X - C (BouquetRing.ε n)) ^ M := by
  rw [map_pow, subst_X]

/-- The composite `k n ≫ σ n ≫ h false` on the restriction of `sec M` to `η n`. -/
theorem k_σ_h_false_c_app_res_sec (n M : ℕ) :
    ((k n ≫ (σ n).hom ≫ h false).toHom.c.app (op (η n))).1
      ((D.presheaf.map (homOfLE (η_le_U false n)).op).1 (sec M)) =
      (((Y.restrict W).restrict (disjointGlueCover pt n)).presheaf.map (homOfLE le_top).op).1
        (((k n).toHom.c.app (op ⊤)).1
          ((spfGammaHom A.α).1 ((X - C (BouquetRing.ε n)) ^ M))) := by
  change ((k n).toHom.c.app _).1 (((σ n).hom.toHom.c.app _).1
    (((h false).toHom.c.app (op (η n))).1
      ((D.presheaf.map (homOfLE (η_le_U false n)).op).1 (sec M)))) = _
  rw [h_false_c_app_res_sec, σ_c_app_res, subst_X_pow]
  exact PresheafedSpace.c_app_map_homOfLE_apply (k n).toHom le_top _

/-- **The key computation.** The copy `true` sends the restriction to `η n` of the section
`sec M`, defined through the copy `false`, to the restriction of `(X - ε n) ^ M`. -/
theorem h_true_c_app_res_sec (n M : ℕ) :
    ((h true).toHom.c.app (op (η n))).1 ((D.presheaf.map (homOfLE (η_le_U false n)).op).1
      (sec M)) =
      (Y.presheaf.map (homOfLE le_top).op).1
        ((spfGammaHom A.α).1 ((X - C (BouquetRing.ε n)) ^ M)) := by
  set V' := (Opens.map (h true).toHom.base).obj (η n) with hV'
  have hsub : (V' : Set Y) ⊆ Set.range (k n).toHom.base := by
    rw [range_k, hV', map_h_η]
  have : IsIso ((k n).toHom.c.app (op V')) :=
    PresheafedSpace.IsOpenImmersion.c_iso' (k n).toHom ((Opens.map (k n).toHom.base).obj V')
      (Opens.ext (Set.image_preimage_eq_of_subset hsub).symm)
  refine TopCommRingCat.injective_of_isIso ((k n).toHom.c.app (op V')) ?_
  refine (PresheafedSpace.c_app_apply_eq_of_eq (congrArg Hom.toHom (k_comp_h_true n)) (η n) _ _
    (k_σ_h_false_c_app_res_sec n M)).trans ?_
  exact (PresheafedSpace.c_app_map_homOfLE_apply (k n).toHom (le_top : V' ≤ ⊤)
    ((spfGammaHom A.α).1 ((X - C (BouquetRing.ε n)) ^ M))).symm

/-- The point `Spec (R⟦X⟧/(X)) ⟶ D` of the copy `true` at the ideal of definition `(X)`. -/
noncomputable def pointTrue : schemeToLTRSObj (Spec (spfQuotient A.α (idealX BouquetRing.R))) ⟶ D :=
  spfChartPoint (isPreAdmissible BouquetRing.R) (e true) (idealX BouquetRing.R)

/-- The point `pointTrue` lands in the copy `U true`. -/
theorem range_pointTrue : Set.range pointTrue.toHom.base ⊆ (U true : Set D) := by
  rintro _ ⟨x, rfl⟩
  exact (mem_U_iff true _).mpr ⟨_, rfl⟩

/-- The kernel of `pointTrue` over `U true` is a neighbourhood of zero. -/
theorem ker_pointTrue_mem_nhds :
    ((IdealSheaf.ker pointTrue).ideal (U true) : Set (D.presheaf.obj (op (U true))).α) ∈
      nhds 0 :=
  (isIdealOfDefinition_ker_spfChartPoint (isPreAdmissible BouquetRing.R) (e true)
    (idealX BouquetRing.R) le_rfl (isCompact_U true)).1.mem_nhds (zero_mem _)

/-- The point at `(X)` does not kill the restriction of `(X - ε) ^ M` to `pt n`, written over any
open equal to `pt n`, as soon as `M ≤ n`. -/
theorem pointX_c_app_res_ne_zero {n M : ℕ} (hM : M ≤ n) {V : Opens Y} (hV : V = pt n) :
    ((pointX BouquetRing.R).toHom.c.app (op V)).1 ((Y.presheaf.map (homOfLE le_top).op).1
      ((spfGammaHom A.α).1 ((X - C (BouquetRing.ε n)) ^ M))) ≠ 0 := by
  subst hV
  exact pointX_c_app_spfBasicOpen_res_X_sub_C_pow_ne_zero _ _ M
    (BouquetRing.algebraMap_ε_pow_ne_zero hM)

/-- **The obstruction.** The point `pointTrue` does not kill the restriction to `η n` of the
section `sec M`, defined through the other copy, as soon as `M ≤ n`. -/
theorem pointTrue_c_app_res_sec_ne_zero {n M : ℕ} (hM : M ≤ n) :
    (pointTrue.toHom.c.app (op (η n))).1
      ((D.presheaf.map (homOfLE (η_le_U false n)).op).1 (sec M)) ≠ 0 := by
  change ((pointX BouquetRing.R).toHom.c.app (op ((Opens.map (h true).toHom.base).obj (η n)))).1
    (((h true).toHom.c.app (op (η n))).1
      ((D.presheaf.map (homOfLE (η_le_U false n)).op).1 (sec M))) ≠ 0
  rw [h_true_c_app_res_sec]
  exact pointX_c_app_res_ne_zero hM (map_h_η true n)

/-- Every open ideal of the sections over `U false` contains `sec M` for some `M`. -/
theorem exists_sec_mem (L : Ideal (D.presheaf.obj (op (U false))).α)
    (hL : IsOpen (L : Set (D.presheaf.obj (op (U false))).α)) : ∃ M, sec M ∈ L := by
  have hc := (spfChartSection (isPreAdmissible BouquetRing.R) (e false)).2
  have hpre : (spfChartSection (isPreAdmissible BouquetRing.R) (e false)).1 ⁻¹' (L : Set _) ∈
      nhds (0 : A.α) :=
    (hL.preimage hc).mem_nhds (by simp)
  obtain ⟨M, hM⟩ := (isAdic_iff.mp (isAdic_span_X BouquetRing.R)).2 _ hpre
  exact ⟨M, hM (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self X) M)⟩

/-- **The twisted double has no fundamental system of ideals of definition cut out by their
sections over the affine formal opens.** -/
theorem not_exists_isCutOutOn_isFundamentalSystemOfIdealsOfDefinitionOn :
    ¬ ∃ 𝒮 : Set (IdealSheaf D), (∀ I ∈ 𝒮, I.IsCutOutOn (IsAffineFormalOpen D)) ∧
        IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen D) := by
  refine
    LocallyTopologicallyRingedSpace.not_exists_isCutOutOn_isFundamentalSystemOfIdealsOfDefinitionOn
    (isAffineFormalOpen_U true) (isAffineFormalOpen_U false) pointTrue range_pointTrue
    ker_pointTrue_mem_nhds fun L hL => ?_
  obtain ⟨M, hM⟩ := exists_sec_mem L hL
  exact ⟨η M, η_le_U true M, η_le_U false M, sec M, hM, pointTrue_c_app_res_sec_ne_zero le_rfl⟩

/-- **The functor of points of the twisted double is not a colimit of schemes along thickenings**
in fppf sheaves, as in Stacks 0AIU. -/
theorem not_isFppfColimitOfThickenings : ¬ 𝔛.toMcQuillanFormalScheme.IsFppfColimitOfThickenings :=
  fun h => not_exists_isCutOutOn_isFundamentalSystemOfIdealsOfDefinitionOn
    ((FormalScheme.isFppfColimitOfThickenings_iff 𝔛).mp h)

end TwistedDouble

end AlgebraicGeometry

end
