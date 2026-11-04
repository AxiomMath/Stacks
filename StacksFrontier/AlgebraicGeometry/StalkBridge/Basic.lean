module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.OnTag01YE.Basic

/-!
# [Stacks, Tag 01YE] implies the hypothesis that Tags 01YG and 01YH rest on

`Stacks.AlgebraicGeometry.Tag01YGOnTag01YE.property_of_hasKilledIdealGenericIsoSub` proves Tag
01YG from `Stacks.AlgebraicGeometry.Tag01YGOnTag01YE.HasKilledIdealGenericIsoSub`, and
`ConfinedDevissage.property_of_irreducible_support_of_topIdeals_of_genericIsoSub`
proves Tag 01YH from the confined form
`ConfinedDevissage.HasKilledIdealGenericIsoSubIn`. Those two predicates are **not** literally
the conclusion of [Stacks, Tag 01YE]: they take as hypothesis that the module is annihilated
**affine-locally** by the ideal sheaf of the closed set, whereas Tag 01YE asks only that its
**stalk at the generic point** be annihilated by the maximal ideal of the local ring, which is
weaker. The two predicates therefore ask for 01YE's conclusion at fewer modules than Tag 01YE
delivers it to.

This file proves the implication between the two hypotheses.
`isMaximalIdealAnnihilated_of_app_killed` is the bridge: a module killed affine-locally by the
sections that a closed immersion `i` sends to zero has its stalk at the image of a generic point
killed by the whole maximal ideal there. The mechanism is `ker_stalkMap_eq_maximalIdeal` — at a
generic point of an integral scheme the stalk is the function field, so the kernel of the stalk map
of a closed immersion is a maximal ideal, hence *the* maximal ideal — read in the direction that
produces a section: `exists_affineOpen_mem_ker_germ_eq` turns an element of the maximal ideal into
a section over an affine neighbourhood that `i` kills, which is exactly what the affine-local
hypothesis consumes.

With the bridge in hand, `HasKilledIdealGenericIsoSubIn` follows from 01YE by taking for `W` the
reduced induced subscheme on `Z` — the subscheme of
`Stacks.AlgebraicGeometry.IdealPowerSmul.closedIdeal Z`, whose integrality is
`IrreducibleDevissage.isIntegral_subscheme_vanishingIdeal_of_isIrreducible` and whose range is `Z`
on the nose.

## Main definitions

* `IsMaximalIdealAnnihilated`: the hypothesis of Tag 01YE, restated over library names — the maximal
  ideal of the local ring at `x` annihilates the stalk of `F` at `x`. This is
  character-for-character the hypothesis of the tagged statement, which is already written
  entirely in Mathlib's vocabulary.
* `HasGenericStalkIdealCoproductSub`: **the conclusion of [Stacks, Tag 01YE] as a predicate on
  `X`**, restated over library names.

## Main results

* `ker_stalkMap_eq_maximalIdeal`: for a closed immersion `i` from an integral scheme and a generic
  point `ξ`, the kernel of `i.stalkMap ξ` is the maximal ideal of the stalk at `i ξ`.
* `exists_affineOpen_mem_ker_germ_eq`: every element of that maximal ideal is the germ of a section
  over an affine open, inside any prescribed neighbourhood, which `i` sends to zero.
* `isMaximalIdealAnnihilated_of_app_killed`: **the bridge** — affine-local annihilation implies
  the stalk hypothesis of Tag 01YE at the image of the generic point.
* `hasKilledIdealGenericIsoSubIn_of_hasGenericStalkIdealCoproductSub` and
  `hasKilledIdealGenericIsoSub_of_hasGenericStalkIdealCoproductSub`: **[Stacks, Tag 01YE] implies
  both predicates**, so Tags 01YG and 01YH rest on the statement of Tag 01YE verbatim, with
  nothing strengthened in any respect.
* `property_of_hasGenericStalkIdealCoproductSub`: **the statement of Tag 01YG verbatim with the
  conclusion of [Stacks, Tag 01YE] as its one added hypothesis.** Tag 01YH is reduced the same
  way by feeding `hasKilledIdealGenericIsoSubIn_of_hasGenericStalkIdealCoproductSub` to
  `ConfinedDevissage.property_of_irreducible_support_of_topIdeals_of_genericIsoSub`,
  whose remaining hypothesis `htop` is independent of 01YE.

## Implementation notes

`exists_affineOpen_mem_ker_germ_eq` is the converse of
`germ_of_section_in_closed_immersion_kernel_mem_maximalIdeal`, and the converse is where the work
is: the vanishing it extracts from the stalk map holds on an open of `W`, and the affine-local
hypothesis is indexed by affine opens of `X`. The step across is the subspace topology of a closed
embedding, `Topology.IsInducing.isOpen_iff`, followed by shrinking inside
`AlgebraicGeometry.Scheme.isBasis_affineOpens`.

**The subscheme is assembled, not built.** No reducedness, irreducibility or integrality argument
appears below: `IrreducibleDevissage.isIntegral_subscheme_vanishingIdeal_of_isIrreducible` is
exactly the needed statement, and
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_vanishingIdeal` supplies the range.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01YEStalkBridge

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### The stalk hypothesis of Tag 01YE -/

/-- **The hypothesis of Tag 01YE.** The maximal ideal of the local ring at `x` annihilates the stalk
of `F` at `x`.

This is the hypothesis of the tagged statement character for character. -/
def IsMaximalIdealAnnihilated {X : Scheme.{u}} (F : X.Modules) (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  ∀ a : X.presheaf.stalk x,
    a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
    ∀ s : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x, a • s = 0

/-! ### The maximal ideal at the image of a generic point -/

variable {X W : Scheme.{u}}

/-- At a generic point of an integral scheme the stalk is the function field, hence a field. -/
theorem isField_stalk_of_genericPoint [IsIntegral W] (ξ : W)
    (hξ : IsGenericPoint ξ (Set.univ : Set W)) :
    IsField (W.presheaf.stalk ξ) := by
  have hξ' : ξ = genericPoint W := hξ.eq (genericPoint_spec W)
  rw [hξ']
  exact Field.toIsField W.functionField

/-- The maximal ideal of the stalk at a generic point of an integral scheme is zero. -/
theorem maximalIdeal_eq_bot_at_genericPoint [IsIntegral W] (ξ : W)
    (hξ : IsGenericPoint ξ (Set.univ : Set W)) :
    IsLocalRing.maximalIdeal (W.presheaf.stalk ξ) = ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mp (isField_stalk_of_genericPoint ξ hξ)

/-- **The kernel of the stalk map of a closed immersion at a generic point of an integral source
is the whole maximal ideal.** The stalk map is surjective, the stalk upstairs is a field, so the
kernel is maximal — and a local ring has only one maximal ideal. -/
theorem ker_stalkMap_eq_maximalIdeal [IsIntegral W] (i : W ⟶ X) [IsClosedImmersion i]
    (ξ : W) (hξ : IsGenericPoint ξ (Set.univ : Set W)) :
    RingHom.ker (i.stalkMap ξ).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i ξ)) := by
  have hf : Function.Surjective (i.stalkMap ξ).hom := i.stalkMap_surjective ξ
  have hbot : (⊥ : Ideal (W.presheaf.stalk ξ)).IsMaximal := by
    rw [← maximalIdeal_eq_bot_at_genericPoint ξ hξ]
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine IsLocalRing.eq_maximalIdeal ?_
  show (Ideal.comap (i.stalkMap ξ).hom (⊥ : Ideal (W.presheaf.stalk ξ))).IsMaximal
  exact Ideal.comap_isMaximal_of_surjective _ hf (K := ⊥) (H := hbot)

/-- **Every element of the maximal ideal at the image of a generic point is the germ of a section
that the closed immersion kills, over an affine open inside any prescribed neighbourhood.**

This is the converse of
`germ_of_section_in_closed_immersion_kernel_mem_maximalIdeal`, and it is the form the affine-local
annihilation hypothesis of `ConfinedDevissage.HasKilledIdealGenericIsoSubIn` can
consume. The vanishing coming out of `ker_stalkMap_eq_maximalIdeal` lives on an open of `W`; it is
transported to an open of `X` by the subspace topology of the closed embedding `i`, and then
shrunk to an affine open. -/
theorem exists_affineOpen_mem_ker_germ_eq [IsIntegral W] (i : W ⟶ X) [IsClosedImmersion i]
    (ξ : W) (hξ : IsGenericPoint ξ (Set.univ : Set W))
    (U₀ : X.Opens) (hU₀ : i ξ ∈ U₀)
    (a : X.presheaf.stalk (i ξ))
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i ξ))) :
    ∃ (V : X.affineOpens) (hV : i ξ ∈ V.1), V.1 ≤ U₀ ∧
      ∃ b : Γ(X, V.1), i.app V.1 b = 0 ∧ X.presheaf.germ V.1 (i ξ) hV b = a := by
  rw [← ker_stalkMap_eq_maximalIdeal i ξ hξ, RingHom.mem_ker] at ha
  obtain ⟨U, hUU₀, hxU, b, hb⟩ := X.presheaf.exists_le_germ_eq a hU₀
  -- The germ of `i.app U b` at `ξ` vanishes.
  have h0 : W.presheaf.germ (i ⁻¹ᵁ U) ξ hxU (i.app U b) = 0 := by
    rw [← Scheme.Hom.germ_stalkMap_apply i U ξ hxU b, hb]
    exact ha
  -- So `i.app U b` vanishes on an open neighbourhood `V'` of `ξ` in `W`.
  obtain ⟨V', hξV', jU, jV, he⟩ :=
    W.presheaf.germ_eq (U := i ⁻¹ᵁ U) (V := i ⁻¹ᵁ U) ξ hxU hxU (i.app U b) 0
      (by rw [h0, map_zero])
  have he' : W.presheaf.map jU.op (i.app U b) = 0 := by rw [he, map_zero]
  -- Transport `V'` across the subspace topology of the closed embedding `i`.
  obtain ⟨t, ht, htV⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V'.2
  have hξt : i ξ ∈ t := by
    have : ξ ∈ i.base ⁻¹' t := by rw [htV]; exact hξV'
    exact this
  have hsub : i ⁻¹ᵁ (⟨t, ht⟩ ⊓ U : X.Opens) ≤ V' := by
    intro w hw
    have : w ∈ i.base ⁻¹' t := hw.1
    rw [htV] at this
    exact this
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show i ξ ∈ ((⟨t, ht⟩ ⊓ U : X.Opens) : Set X) from ⟨hξt, hxU⟩)
      (⟨t, ht⟩ ⊓ U : X.Opens).2
  have hVle' : V ≤ (⟨t, ht⟩ ⊓ U : X.Opens) := hVle
  have hVU : V ≤ U := hVle'.trans inf_le_right
  refine ⟨⟨V, hVaff⟩, hxV, hVU.trans hUU₀, X.presheaf.map (homOfLE hVU).op b, ?_, ?_⟩
  · -- `i.app V` of the restricted section is a further restriction of `i.app U b`, which is zero.
    have hpre : i ⁻¹ᵁ V ≤ V' := le_trans (i.preimage_mono hVle') hsub
    have hnat := congrArg (fun f : Γ(X, U) ⟶ Γ(W, i ⁻¹ᵁ V) => f b)
      (i.naturality (homOfLE hVU).op)
    simp only [ConcreteCategory.comp_apply, Quiver.Hom.unop_op] at hnat
    have hfac : (Opens.map i.base).map (homOfLE hVU) = homOfLE hpre ≫ jU := rfl
    rw [hnat, hfac, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, he', map_zero]
  · exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) (i ξ) hxV b).trans hb

/-! ### The bridge -/

/-- Scalar multiplication commutes with taking germs, with the scalar read in `X.presheaf` rather
than in the sheaf of rings underlying `X.Modules`. The two spellings are definitionally equal but
not syntactically so, which defeats `rw`; this is `PresheafOfModules.germ_smul` restated at the
spelling `IsMaximalIdealAnnihilated` uses. -/
theorem germ_smul (G : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) (s : Γ(G, U)) :
    (letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
     TopCat.Presheaf.germ G.val.presheaf U x hx (r • s) =
       X.presheaf.germ U x hx r • TopCat.Presheaf.germ G.val.presheaf U x hx s) :=
  PresheafOfModules.germ_smul G.val x U hx r s

/-- **The bridge from affine-local annihilation to the stalk hypothesis of Tag 01YE.** If every
section that the closed immersion `i` sends to zero annihilates the sections of `F` over the same
affine open, then the stalk of `F` at the image of a generic point of `W` is annihilated by the
whole maximal ideal there.

This is the residual between the hypothesis of Tag 01YE and the hypothesis of
`Stacks.AlgebraicGeometry.Tag01YGOnTag01YE.HasKilledIdealGenericIsoSub`, which that
declaration's implementation notes name. Neither coherence nor
quasi-coherence of `F` is used, and `X` need not be Noetherian. -/
theorem isMaximalIdealAnnihilated_of_app_killed [IsIntegral W] (i : W ⟶ X)
    [IsClosedImmersion i] (ξ : W) (hξ : IsGenericPoint ξ (Set.univ : Set W))
    (F : X.Modules)
    (hkill : ∀ (V : X.affineOpens) (b : Γ(X, V.1)), i.app V.1 b = 0 →
      ∀ m : Γ(F, V.1), b • m = 0) :
    IsMaximalIdealAnnihilated F (i ξ) := by
  intro a ha s
  obtain ⟨U₀, hU₀, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf s
  obtain ⟨V, hV, hVU₀, b, hb0, hbg⟩ :=
    exists_affineOpen_mem_ker_germ_eq i ξ hξ U₀ hU₀ a ha
  let t' : Γ(F, V.1) := F.val.presheaf.map (homOfLE hVU₀).op t
  have hts : TopCat.Presheaf.germ F.val.presheaf V.1 (i ξ) hV t' = s := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact ht
  have key : TopCat.Presheaf.germ F.val.presheaf V.1 (i ξ) hV
      ((show Γ(X, V.1) from b) • t') = 0 := by
    rw [hkill V b hb0 t']
    exact map_zero _
  rw [germ_smul F (i ξ) V.1 hV b t'] at key
  rw [← hbg, ← hts]
  exact key

/-! ### [Stacks, Tag 01YE] as a predicate -/

/-- **The conclusion of [Stacks, Tag 01YE], restated over library names.** For every closed
immersion `i : W ⟶ X` with `W` integral, every generic point `ξ` of `W`, and every coherent `F`
whose stalk at `i ξ` is annihilated by the maximal ideal there, a finite coproduct of copies of
one coherent ideal sheaf on `W` maps monomorphically into `F`, coherently, and invertibly on a
neighbourhood of `i ξ`.

This is the conclusion of the tagged statement with its instance arguments
spelled out and its `let` inlined; nothing is added, removed or weakened. -/
def HasGenericStalkIdealCoproductSub (X : Scheme.{u}) : Prop :=
  ∀ (W : Scheme.{u}) (i : W ⟶ X), IsClosedImmersion i → IsIntegral W →
    ∀ ξ : W, IsGenericPoint ξ (Set.univ : Set W) →
      ∀ F : X.Modules, F.IsCoherent → IsMaximalIdealAnnihilated F (i ξ) →
        ∃ (r : ℕ) (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
          I.toSheafOfModules.IsCoherent ∧
          ((Scheme.Modules.pushforward i).obj
            (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent ∧
          ∃ φ : (Scheme.Modules.pushforward i).obj
              (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ F,
            Mono φ ∧ ∃ U : X.Opens, i ξ ∈ U ∧
              IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)

/-- **[Stacks, Tag 01YE] implies the confined hypothesis that [Stacks, Tag 01YH] consumes.**

The subscheme `W` is the reduced induced structure on `Z`, so its range is `Z` exactly and its
generic point is a point of `Z`; `isIntegral_subscheme_closedIdeal` makes it integral, and
`isMaximalIdealAnnihilated_of_app_killed` converts the affine-local annihilation hypothesis into
the stalk hypothesis of Tag 01YE through
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app`. -/
theorem hasKilledIdealGenericIsoSubIn_of_hasGenericStalkIdealCoproductSub
    (X : Scheme.{u}) (h : HasGenericStalkIdealCoproductSub X) :
    ConfinedDevissage.HasKilledIdealGenericIsoSubIn X := by
  intro Z hZirr Q hQq hQc hkill
  have hWint : IsIntegral (IdealPowerSmul.closedIdeal Z).subscheme :=
    IrreducibleDevissage.isIntegral_subscheme_vanishingIdeal_of_isIrreducible Z hZirr
  have hrange : Set.range (IdealPowerSmul.closedIdeal Z).subschemeι.base = (Z : Set X) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z
  have hξ : IsGenericPoint (genericPoint (IdealPowerSmul.closedIdeal Z).subscheme)
      (Set.univ : Set (IdealPowerSmul.closedIdeal Z).subscheme) := genericPoint_spec _
  have hξZ : (IdealPowerSmul.closedIdeal Z).subschemeι
      (genericPoint (IdealPowerSmul.closedIdeal Z).subscheme) ∈ (Z : Set X) :=
    hrange ▸ Set.mem_range_self _
  -- The affine-local annihilation hypothesis in the form the bridge consumes.
  have hkill' : ∀ (V : X.affineOpens) (b : Γ(X, V.1)),
      (IdealPowerSmul.closedIdeal Z).subschemeι.app V.1 b = 0 →
        ∀ m : Γ(Q, V.1), b • m = 0 := by
    intro V b hb m
    have hbD : b ∈ (IdealPowerSmul.closedIdeal Z).ideal V := by
      rw [← Scheme.IdealSheafData.ker_subschemeι_app (IdealPowerSmul.closedIdeal Z) V,
        RingHom.mem_ker]
      exact hb
    have hmem : b • m ∈ (IdealPowerSmul.closedIdeal Z).ideal V •
        (⊤ : Submodule Γ(X, V.1) Γ(Q, V.1)) :=
      Submodule.smul_mem_smul hbD Submodule.mem_top
    rw [hkill V, Submodule.mem_bot] at hmem
    exact hmem
  obtain ⟨r, I, hIc, hAc, φ, hmono, U, hU, hiso⟩ :=
    h (IdealPowerSmul.closedIdeal Z).subscheme (IdealPowerSmul.closedIdeal Z).subschemeι
      inferInstance hWint
      (genericPoint (IdealPowerSmul.closedIdeal Z).subscheme) hξ Q hQc
      (isMaximalIdealAnnihilated_of_app_killed _ _ hξ Q hkill')
  have hIq : I.toSheafOfModules.IsQuasicoherent :=
    have := hIc
    isQuasicoherent_of_isCoherent _
  exact ⟨(IdealPowerSmul.closedIdeal Z).subscheme, (IdealPowerSmul.closedIdeal Z).subschemeι,
    inferInstance,
    hWint, r, I, hIq, hrange.le, hAc, φ, hmono, U, _, hU, hξZ, hiso⟩

/-- **[Stacks, Tag 01YE] implies the unconfined hypothesis that Tag 01YG rests on**, by
forgetting the containment. -/
theorem hasKilledIdealGenericIsoSub_of_hasGenericStalkIdealCoproductSub
    (X : Scheme.{u}) (h : HasGenericStalkIdealCoproductSub X) :
    Tag01YGOnTag01YE.HasKilledIdealGenericIsoSub X :=
  Tag01YGOnTag01YE.hasKilledIdealGenericIsoSub_of_hasKilledIdealGenericIsoSubIn
    (hasKilledIdealGenericIsoSubIn_of_hasGenericStalkIdealCoproductSub X h)

/-- **The statement of Tag 01YG verbatim, with the conclusion of [Stacks, Tag 01YE] itself as its one
added hypothesis** — no containment condition, no affine-local annihilation, nothing strengthened
in any respect.

`Stacks.AlgebraicGeometry.Tag01YGOnTag01YE.property_of_hasKilledIdealGenericIsoSub` had already
reduced Tag 01YG to `HasKilledIdealGenericIsoSub`, which asks for 01YE's conclusion only at
modules annihilated *affine-locally* — a hypothesis strictly stronger than 01YE's, so that
reduction was not yet a reduction to 01YE. Composing it with
`hasKilledIdealGenericIsoSub_of_hasGenericStalkIdealCoproductSub` closes the difference: the only
hypothesis left is Tag 01YE. -/
theorem property_of_hasGenericStalkIdealCoproductSub (X : Scheme.{u}) [IsNoetherian X]
    (h : HasGenericStalkIdealCoproductSub X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  Tag01YGOnTag01YE.property_of_hasKilledIdealGenericIsoSub X
    (hasKilledIdealGenericIsoSub_of_hasGenericStalkIdealCoproductSub X h) P hzero hext hideal

end Stacks.AlgebraicGeometry.Tag01YEStalkBridge

end
