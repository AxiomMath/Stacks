module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepCokernelDim
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepEuler
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingUnitsSequence
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingPicardSequence
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingProducer

/-!
# `dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` for the two elementary steps

This file feeds the germ-local data of the two elementary steps of [Stacks, Tag 0C1L] into
`Stacks.GlueSquishFactor.finrank_cohomologyOverField_zero_cokernel_eq_one` and reads off

`dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1`

for a glueing of two rational points and for a squishing of a tangent vector.

For a glueing the rule is the difference `s ↦ s(a) - s(b)` of the evaluations at the two glued
points: it is additive and multiplicative because each evaluation is a ring homomorphism, it is
`k`-homogeneous because the pullback of a constant is a constant
(`Stacks.GlueSquishFactor.app_constHom`) and a constant evaluates to itself
(`AlgebraicGeometry.sectionAt_constHom`), it kills the pullbacks from `X` because the two points
have the same image, and the last two clauses of `AlgebraicGeometry.IsGlueingTwoPoints` are
exactly the surjectivity and the exactness in the middle that the criterion asks for.

For a squishing the rule is the coefficient of `ε` along the squished tangent vector. Here the
predicate carries an honest short exact sequence of sheaves of abelian groups, so the vanishing
on pullbacks from `X` is the composite of its two maps being zero, the exactness in the middle
is left exactness of evaluation at an open, and the nonvanishing is the surjectivity of its
second map: a map onto the skyscraper which were zero on every open would make the skyscraper a
zero object, and the skyscraper's sections are the ground field.

## Main results

All in the namespace `Stacks.GlueSquishFactor`:

* `finrank_cohomologyOverField_zero_cokernel_eq_one_of_isGlueingTwoPoints`
* `finrank_cohomologyOverField_zero_cokernel_eq_one_of_isSquishingTangentVector`
* `genus_eq_add_one_of_isGlueingTwoPoints` and `genus_eq_add_one_of_isSquishingTangentVector` —
  the resulting `genus(X) = genus(X') + 1`.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-! ### Glueing two rational points -/

/-- **`dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` for a glueing of two rational points.** The germ-local
rule is the difference of the evaluations at the two glued points; the last two clauses of
`AlgebraicGeometry.IsGlueingTwoPoints` are the surjectivity of that rule and the descent of a
section on which it vanishes. -/
theorem finrank_cohomologyOverField_zero_cokernel_eq_one_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) :
    Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
      (cokernel (structureUnitHom f)) 0) = 1 := by
  obtain ⟨ha, hb, -, hfover, -, -, -, -, hab, -, ⟨W, hWset, hWiso⟩, -, hdesc, hsurj⟩ := h
  have := hWiso
  have hmemB : ∀ (U : X.Opens), (a ≫ f).base (IsLocalRing.closedPoint k) ∈ U →
      b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U := by
    intro U hU
    have hbase := congrArg (fun g : Spec (.of k) ⟶ X => g.base (IsLocalRing.closedPoint k)) hab
    change f.base (a.base _) = f.base (b.base _) at hbase
    show f.base (b.base _) ∈ U
    rw [← hbase]
    exact hU
  have hxB : ∀ (U : X.Opens), (a ≫ f).base (IsLocalRing.closedPoint k) ∈ U →
      (b ≫ f).base (IsLocalRing.closedPoint k) ∈ U := fun U hU => hmemB U hU
  refine finrank_cohomologyOverField_zero_cokernel_eq_one f hWset
    (fun U hU s => AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU s -
      AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) s) ?_ ?_ ?_ ?_ ?_ ?_
  · intro U hU s t
    have hA : AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU (s + t) =
        AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU s +
          AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU t :=
      map_add (AlgebraicGeometry.sectionAtHom a (f ⁻¹ᵁ U) hU) s t
    have hB : AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) (s + t) =
        AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) s +
          AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) t :=
      map_add (AlgebraicGeometry.sectionAtHom b (f ⁻¹ᵁ U) (hmemB U hU)) s t
    show AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU (s + t) -
      AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) (s + t) = _
    rw [hA, hB]
    ring
  · intro U V hVU hV s
    show AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ V) hV _ -
      AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ V) (hmemB V hV) _ = _
    rw [AlgebraicGeometry.sectionAt_map a (homOfLE (f.preimage_mono hVU)) hV s,
      AlgebraicGeometry.sectionAt_map b (homOfLE (f.preimage_mono hVU)) (hmemB V hV) s]
  · intro U hU c s
    rw [app_constHom f hfover U (by simp) (by simp) c]
    have hmula : ∀ y z : Γ(X', f ⁻¹ᵁ U),
        AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU (y * z) =
          AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU y *
            AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU z :=
      fun y z => map_mul (AlgebraicGeometry.sectionAtHom a (f ⁻¹ᵁ U) hU) y z
    have hmulb : ∀ y z : Γ(X', f ⁻¹ᵁ U),
        AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) (y * z) =
          AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) y *
            AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) z :=
      fun y z => map_mul (AlgebraicGeometry.sectionAtHom b (f ⁻¹ᵁ U) (hmemB U hU)) y z
    have hca := AlgebraicGeometry.sectionAt_constHom a ha (f ⁻¹ᵁ U) hU (by simp) c
    have hcb := AlgebraicGeometry.sectionAt_constHom b hb (f ⁻¹ᵁ U) (hmemB U hU) (by simp) c
    show AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU _ -
      AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) _ = _
    rw [hmula, hmulb, hca, hcb]
    ring
  · intro U hU t
    show AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) hU _ -
      AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) (hmemB U hU) _ = 0
    rw [Stacks.GlueSquishUnits.sectionAt_pullback' f a U hU hU t,
      Stacks.GlueSquishUnits.sectionAt_pullback' f b U (hxB U hU) (hmemB U hU) t,
      Stacks.GlueSquishUnits.sectionAt_congr' hab U hU (hxB U hU) t, sub_self]
  · obtain ⟨U, hxU, s, hs⟩ := hsurj 1
    exact ⟨U, hxU, s, fun hz => one_ne_zero (hs.symm.trans hz)⟩
  · exact hdesc

/-! ### Squishing a tangent vector -/

/-- **A tangent vector defined over `k` restricts a constant section to the corresponding
constant dual number**, over any neighbourhood of the contracted point. This is
`Stacks.SquishSheafSequence.germ_stalkClosedPointTo_const'` read on a constant section over an
open rather than over the whole space. -/
theorem sectionsToDualNumber_constHom {k : Type u} [Field k] {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] (η : Spec (.of (DualNumber k)) ⟶ Y)
    (hη : η ≫ (Y ↘ Spec (.of k)) = dualNumberToBase k) (U : Y.Opens)
    (hU : η.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U)
    (hUle : U ≤ (Y ↘ Spec (.of k)) ⁻¹ᵁ ⊤) (c : k) :
    Stacks.SquishSheafSequence.sectionsToDualNumber η U hU (constHom Y U hUle c)
      = algebraMap k (DualNumber k) c := by
  have hres : (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (constHom Y ⊤ (by simp) c) = constHom Y U hUle c :=
    constHom_res (le_top : U ≤ ⊤) (by simp) hUle c
  rw [← hres, Stacks.SquishSheafSequence.sectionsToDualNumber_res η (le_top : U ≤ ⊤) hU
    (constHom Y ⊤ (by simp) c), constHom_top Y (by simp) c]
  exact Stacks.SquishSheafSequence.germ_stalkClosedPointTo_const' η hη c

/-- An epimorphism onto the additive skyscraper sheaf with fibre `k` is nonzero. -/
theorem ne_zero_of_epi_skyscraperAddSheaf {k : Type u} [Field k] {X : Scheme.{u}} {x : X}
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (ψ : F ⟶ skyscraperAddSheaf (k := k) X x)
    [Epi ψ] : ψ ≠ 0 := by
  intro hψ0
  have hid : 𝟙 (skyscraperAddSheaf (k := k) X x) = 0 :=
    (cancel_epi ψ).mp (by rw [Category.comp_id, hψ0, Limits.zero_comp])
  have hone :
      Stacks.SquishSheafSequence.skyscraperAddSheafMk X x (Opens.mem_top x) (1 : k) = 0 :=
    congrArg (fun m : skyscraperAddSheaf (k := k) X x ⟶ skyscraperAddSheaf (k := k) X x =>
      ConcreteCategory.hom (m.hom.app (op (⊤ : X.Opens)))
        (Stacks.SquishSheafSequence.skyscraperAddSheafMk X x (Opens.mem_top x) (1 : k))) hid
  exact one_ne_zero (Stacks.SquishSheafSequence.skyscraperAddSheafMk_injective (k := k) X x
    (Opens.mem_top x) (hone.trans
      (Stacks.SquishSheafSequence.skyscraperAddSheafMk_zero (k := k) X x (Opens.mem_top x)).symm))

/-- **`dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` for a squishing of a tangent vector.** The germ-local
rule is the coefficient of `ε` along the squished vector; the short exact sequence of sheaves of
abelian groups carried by `AlgebraicGeometry.IsSquishingTangentVector` supplies the vanishing on
pullbacks from `X`, the descent of a section on which the rule vanishes, and — through the
surjectivity of its second map — the existence of a section on which it does not. -/
theorem finrank_cohomologyOverField_zero_cokernel_eq_one_of_isSquishingTangentVector
    {k : Type u} [Field k] [IsAlgClosed k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) :
    Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
      (cokernel (structureUnitHom f)) 0) = 1 := by
  obtain ⟨ψ, hzero, hshort, hψ⟩ :=
    Stacks.SquishSheafSequence.shortExact_of_isSquishingTangentVector f θ h
  obtain ⟨hfover, -, -, -, -, -, hθ, -, -, -, -, ⟨W, hWset, hWiso⟩, -⟩ := h
  have := hWiso
  have := hshort.epi_g
  refine finrank_cohomologyOverField_zero_cokernel_eq_one f hWset
    (fun U hU s => AlgebraicGeometry.epsilonCoefficientAt θ (f ⁻¹ᵁ U) hU s) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun U hU s t => map_add (epsilonCoefficientAddHom θ (f ⁻¹ᵁ U) hU) s t
  · exact fun U V hVU hV s => epsilonCoefficientAt_res θ (f.preimage_mono hVU) hV s
  · intro U hU c s
    rw [app_constHom f hfover U (by simp) (by simp) c]
    have hmul : Stacks.SquishSheafSequence.sectionsToDualNumber θ (f ⁻¹ᵁ U) hU
          (constHom X' (f ⁻¹ᵁ U) (by simp) c * s) =
        Stacks.SquishSheafSequence.sectionsToDualNumber θ (f ⁻¹ᵁ U) hU
            (constHom X' (f ⁻¹ᵁ U) (by simp) c) *
          Stacks.SquishSheafSequence.sectionsToDualNumber θ (f ⁻¹ᵁ U) hU s :=
      map_mul _ _ _
    have hc := sectionsToDualNumber_constHom θ hθ (f ⁻¹ᵁ U) hU (by simp) c
    show (Stacks.SquishSheafSequence.sectionsToDualNumber θ (f ⁻¹ᵁ U) hU
      (constHom X' (f ⁻¹ᵁ U) (by simp) c * s)).snd = _
    rw [hmul, hc, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul]
    exact congrArg (fun y : k => c * y)
      (Stacks.SquishSheafSequence.snd_sectionsToDualNumber θ (f ⁻¹ᵁ U) hU s)
  · intro U hU t
    refine Stacks.SquishSheafSequence.skyscraperAddSheafMk_injective X _ hU ?_
    rw [Stacks.SquishSheafSequence.skyscraperAddSheafMk_zero,
      ← hψ U hU ((f.app U).hom t)]
    exact congrArg (fun m : Stacks.SquishSheafSequence.structureAddSheaf X ⟶
        AlgebraicGeometry.skyscraperAddSheaf (k := k) X
          ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) =>
      ConcreteCategory.hom (m.hom.app (op U)) t) hzero
  · by_contra hcon
    have hvan : ∀ (V : X.Opens)
        (hV : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ V)
        (s : Γ(X', f ⁻¹ᵁ V)),
        AlgebraicGeometry.epsilonCoefficientAt θ (f ⁻¹ᵁ V) hV s = 0 :=
      fun V hV s => not_not.mp fun hne => hcon ⟨V, hV, s, hne⟩
    have hcomp : ∀ (V : X.Opens) (s : Γ(X', f ⁻¹ᵁ V)), ψ.hom.app (op V) s = 0 := by
      intro V s
      by_cases hxV : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ V
      · rw [hψ V hxV s, hvan V hxV s,
          Stacks.SquishSheafSequence.skyscraperAddSheafMk_zero]
      · exact Stacks.SquishSheafSequence.skyscraperAddSheaf_eq_zero X _ V hxV _
    refine ne_zero_of_epi_skyscraperAddSheaf ψ ?_
    apply Sheaf.hom_ext
    ext V s
    exact hcomp V.unop s
  · intro U hU s hs
    have hψ0 : ψ.hom.app (op U) s = 0 := by
      rw [hψ U hU s, hs, Stacks.SquishSheafSequence.skyscraperAddSheafMk_zero]
    obtain ⟨t, ht⟩ := TopCat.Sheaf.sections_exact_of_left_exact (U := U) hshort.exact
      hshort.mono_f s hψ0
    refine ⟨U, le_rfl, hU, t, ?_⟩
    have hres : (X'.presheaf.map (homOfLE (f.preimage_mono (le_refl U))).op).hom s = s := by
      simp
    exact hres.trans ht.symm

/-! ### The genus across an elementary step -/

/-- **The genus rises by exactly one when two rational points on the same connected component of
a proper `X'` are glued.** Combining
`Stacks.GlueSquishFactor.genus_eq_add_finrank_of_finrank_globalSections_eq` with the evaluation
`dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` and with the equality of global sections
`Stacks.GlueSquishFactor.finrank_globalSections_eq_of_isGlueingTwoPoints`. -/
theorem genus_eq_add_one_of_isGlueingTwoPoints (k : Type u) [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    [IsProper (X ↘ Spec (.of k))] [IsProper (X' ↘ Spec (.of k))]
    (hcc : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) =
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k)))
    (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1) :
    (genus (X ↘ Spec (.of k)) : ℤ) = (genus (f ≫ X ↘ Spec (.of k)) : ℤ) + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfin, ⟨W, hWset, hWiso⟩, hker, -, -⟩ := id h
  have := hfin
  have := hWiso
  have hkerloc : ∀ (Ω : X.Opens),
      (a ≫ f).base (IsLocalRing.closedPoint k) ∈ Ω → ∀ s : Γ(X, Ω), (f.app Ω).hom s = 0 →
      ∃ (V : X.Opens) (hVΩ : V ≤ Ω),
        (a ≫ f).base (IsLocalRing.closedPoint k) ∈ V ∧
          (X.presheaf.map (homOfLE hVΩ).op).hom s = 0 := by
    intro Ω hx s hs
    obtain ⟨V, hVΩ, hxV, hV0⟩ := hker Ω hx s ⟨Ω, le_rfl, hx, by rw [hs, map_zero]⟩
    exact ⟨V, hVΩ, hxV, hV0⟩
  have hinj := injective_app_of_isIso_of_locally f hWset hkerloc
  have hmono := mono_hom_pushforwardAlgebra_of_injective_app f fun y => by
    obtain ⟨V, hV, hyV, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) (Opens.mem_top y)
    exact ⟨V, hV, hyV, hinj V⟩
  have hmain := genus_eq_add_finrank_of_finrank_globalSections_eq k f (X ↘ Spec (.of k))
    hmono hWset hdim hdim'
    (finrank_globalSections_eq_of_isGlueingTwoPoints f a b h hcc)
  rw [hmain, finrank_cohomologyOverField_zero_cokernel_eq_one_of_isGlueingTwoPoints f a b h]
  norm_num

/-- **The genus rises by exactly one when a tangent vector of a proper reduced `X'` is
squished.** Combining
`Stacks.GlueSquishFactor.genus_eq_add_finrank_of_finrank_globalSections_eq` with the evaluation
`dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` and with the equality of global sections
`Stacks.GlueSquishFactor.finrank_globalSections_eq_of_isSquishingTangentVector`. -/
theorem genus_eq_add_one_of_isSquishingTangentVector (k : Type u) [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    [IsProper (X ↘ Spec (.of k))] [IsProper (X' ↘ Spec (.of k))]
    [AlgebraicGeometry.IsReduced X']
    (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1) :
    (genus (X ↘ Spec (.of k)) : ℤ) = (genus (f ≫ X ↘ Spec (.of k)) : ℤ) + 1 := by
  obtain ⟨ψ, hzero, hshort, -⟩ :=
    Stacks.SquishSheafSequence.shortExact_of_isSquishingTangentVector f θ h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfin, ⟨W, hWset, hWiso⟩, -⟩ := id h
  have := hfin
  have := hWiso
  have := hshort.mono_f
  have : Mono (Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f).hom :=
    Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
      (Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f)
  have hinj : ∀ U : X.Opens, Function.Injective (f.app U).hom := fun U =>
    (AddCommGrpCat.mono_iff_injective
      ((Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f).hom.app (op U))).mp
      inferInstance
  have hmono := mono_hom_pushforwardAlgebra_of_injective_app f fun y => by
    obtain ⟨V, hV, hyV, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) (Opens.mem_top y)
    exact ⟨V, hV, hyV, hinj V⟩
  have hmain := genus_eq_add_finrank_of_finrank_globalSections_eq k f (X ↘ Spec (.of k))
    hmono hWset hdim hdim'
    (finrank_globalSections_eq_of_isSquishingTangentVector f θ h)
  rw [hmain,
    finrank_cohomologyOverField_zero_cokernel_eq_one_of_isSquishingTangentVector f θ h]
  norm_num

end Stacks.GlueSquishFactor

end
