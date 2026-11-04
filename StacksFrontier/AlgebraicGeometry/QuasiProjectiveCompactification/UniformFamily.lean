module

public import StacksFrontier.AlgebraicGeometry.ChartImmersionFinish.Basic
public import StacksFrontier.AlgebraicGeometry.ProductFamilyRatio.Basic
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic

/-!
# Generating families with immersive pinned morphisms, in one degree over a finite affine cover

Let `f : X ⟶ S` be locally of finite type and `L` an ample invertible `𝒪_X`-module. For every
sufficiently large `d` the power `L ^⊗ d` carries a finite generating family of global sections
whose pinned morphism to projective space over `S` is an immersion
(`Stacks.ProductFamilyTwist.FamilyImmersionTwist`). If `L` is only ample relative to `f` and `S`
is quasi-compact, the same holds over every member of a finite affine open covering of `S`, in one
degree common to all members.

This is the input of the proof of [Stacks, Tag 07RM] that chooses, over each member `V_j` of a
finite affine covering of the base, sections of one power of `L` over `f⁻¹(V_j)` defining an
immersion `f⁻¹(V_j) ⟶ ℙⁿ_{V_j}`. Unlike
`Stacks.VeryAmplePowersUniformDegree.exists_finite_affine_cover_eventually_hasImmersionTwistOver`
it keeps the sections, which is what the proof consumes.

## Main results

* `Stacks.QuasiProjectiveCompactification.eventually_familyImmersionTwist`: the absolute
  statement, every degree from some bound on.
* `Stacks.QuasiProjectiveCompactification.exists_finite_affine_cover_familyImmersionTwist`: the
  relative statement over a finite affine covering, in one positive degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.ProductFamilyTwist RingedSpaceModuleAdjunction

universe u

namespace Stacks.QuasiProjectiveCompactification

/-- **Every sufficiently high power of an ample invertible module carries a generating family
whose pinned morphism to projective space is an immersion.** The base degree is the one of
`Stacks.ChartImmersionFinish.chartImmersion`; the induction step multiplies by a generating
family of the complementary degree, `Stacks.ProductFamilyRatio.productFamilyImmersion`. -/
theorem eventually_familyImmersionTwist {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) [hft : LocallyOfFiniteType f] :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → FamilyImmersionTwist f L d := by
  obtain ⟨N, -, hfam⟩ := exists_familyImmersionTwist_of_chartImmersion f L
    (Stacks.ChartImmersionFinish.chartImmersion f L) hL hft
  obtain ⟨d₁, hd₁⟩ := Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple L hL
  refine ⟨N.toNat + d₁.toNat, fun d hd => ?_⟩
  have hdz : ((N.toNat : ℤ)) + ((d₁.toNat : ℤ)) ≤ (d : ℤ) := by exact_mod_cast hd
  have hb : d₁ ≤ (d : ℤ) - N := by omega
  obtain ⟨m, t, ht⟩ := hd₁ _ hb
  have key := familyImmersionTwist_add f L (Stacks.ProductFamilyRatio.productFamilyImmersion f L)
    hfam ht
  rwa [show N + ((d : ℤ) - N) = (d : ℤ) from by ring] at key

/-- **Over a finite affine covering of a quasi-compact base, one positive degree works for every
member.** For `L` ample relative to `f` and `f` locally of finite type, there are finitely many
affine opens `V_j` covering `S` and a `d ≥ 1` such that over each `V_j` the restriction of `L`
to `f⁻¹(V_j)` has a generating family of global sections of its `d`-th power whose pinned
morphism to `ℙⁿ_{V_j}` is an immersion. -/
theorem exists_finite_affine_cover_familyImmersionTwist {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [CompactSpace S] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Opens),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
        ∃ d : ℕ, 1 ≤ d ∧ ∀ j, FamilyImmersionTwist (f ∣_ V j)
          ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L) d := by
  classical
  set 𝒰 := S.affineCover.finiteSubcover with h𝒰
  have hVaff : ∀ j : 𝒰.I₀, IsAffineOpen (𝒰.f j).opensRange := fun j =>
    isAffineOpen_opensRange _
  choose d₀ hd using fun j : 𝒰.I₀ =>
    eventually_familyImmersionTwist (f ∣_ (𝒰.f j).opensRange) _ (hL.2 _ (hVaff j))
  refine ⟨𝒰.I₀, inferInstance, fun j => (𝒰.f j).opensRange, hVaff,
    Scheme.OpenCover.iSup_opensRange 𝒰, max 1 (Finset.univ.sup d₀), le_max_left _ _,
    fun j => hd j _ ?_⟩
  exact le_trans (Finset.le_sup (Finset.mem_univ j)) (le_max_right _ _)

end Stacks.QuasiProjectiveCompactification

end
