module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFlat
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedOpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin class of a section of a smooth morphism

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `p : P ⟶ X` be a
smooth morphism of schemes locally of finite type over `S` and let `s : X ⟶ P` be a section of `p`.
Then `s` is a regular immersion (Stacks 067R), and

  `1 = s^! ∘ p^*` in `A^*(X)^∧`,

where `s^! = c(X ⟶ P, 𝒩_{X/P})` is the class of section 42.54 of the Stacks Project for the
normal sheaf of the regular immersion `s` (Stacks 0FBQ (3)), `p^* ∈ A^*(P ⟶ X)^∧` is the flat
pullback of Stacks 0B78, and the composite (Stacks 0FE0) is a class for `s ∘ p = id_X`.

## Main results

* `Stacks.Chow.completedBivariantCompositeOfInvertible_completedFlatPullbackOfSmooth_of_section`
  — `1 = s^! ∘ p^*` in `A^*(X)^∧`, the class `s^!` being formed from the regularity of `s`,
  `Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section`.
* `Stacks.Chow.bivariantIdentityClassOfInvertible_capFundamentalFormula` and
  `Stacks.Chow.hasCapFundamentalFormula_completedIdentityClass` — the unit caps fundamental classes
  to fundamental classes.

## References

* [Stacks Project, Tag 0FF1](https://stacks.math.columbia.edu/tag/0FF1)
* [Stacks Project, Tag 067R](https://stacks.math.columbia.edu/tag/067R)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The unit caps fundamental classes to fundamental classes -/

/-- `Stacks.Chow.BivariantClass.CapFundamentalFormula` holds for one of two heterogeneously equal
classes for morphisms into the connected components of `Y` at equal indices if and only if it holds
for the other. -/
theorem BivariantClass.capFundamentalFormula_iff_of_heq (C : ChowSituation.{u})
    (G : GysinSystem C) {W Y : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [LocallyConnectedSpace Y]
    {j₁ j₂ : _root_.ConnectedComponents Y} (hj : j₁ = j₂)
    {u₁ : W ⟶ (Y.connectedComponentOpens j₁ : Scheme.{u})} [LocallyOfFiniteType u₁]
    {u₂ : W ⟶ (Y.connectedComponentOpens j₂ : Scheme.{u})} [LocallyOfFiniteType u₂]
    (hu : u₁ ≍ u₂) {h₁ : u₁ ≫ ((Y.connectedComponentOpens j₁).ι ≫ sY) = sW}
    {h₂ : u₂ ≫ ((Y.connectedComponentOpens j₂).ι ≫ sY) = sW} {p : ℤ}
    {x₁ : BivariantClass C G sW ((Y.connectedComponentOpens j₁).ι ≫ sY) u₁ h₁ p}
    {x₂ : BivariantClass C G sW ((Y.connectedComponentOpens j₂).ι ≫ sY) u₂ h₂ p}
    (hx : x₁ ≍ x₂) (n : ℤ) :
    x₁.CapFundamentalFormula C G sW _ u₁ h₁ n ↔ x₂.CapFundamentalFormula C G sW _ u₂ h₂ n := by
  subst hj
  obtain rfl := eq_of_heq hu
  obtain rfl := eq_of_heq hx
  rfl

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The unit satisfies the formula over Cohen–Macaulay test schemes.** The class
`1 ∈ A^0(X)` satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree `n`:
capping with it sends `[T]_n` to `[X ×_X T]_n`. -/
theorem bivariantIdentityClassOfInvertible_capFundamentalFormula (n : ℤ) :
    (bivariantIdentityClassOfInvertible C sX).CapFundamentalFormula C _ sX sX (𝟙 X)
      (Category.id_comp sX) n := by
  intro T t _ _ _ _
  refine eq_of_heq ((bivariantIdentityClassOfInvertible_cap_heq C sX t n _).trans ?_)
  rw [chowPushforwardOfIso_fundamentalChowClass]
  exact fundamentalChowClass_heq C _ (by ring)

/-- **The unit of `A^*(X)^∧` satisfies the formula componentwise.** On every connected component
of `X` the unit `1 ∈ A^*(X)^∧` is concentrated in degree `0`, where it is `1` and satisfies
`Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree. -/
theorem hasCapFundamentalFormula_completedIdentityClass [IsLocallyNoetherian X] :
    completedBivariantGroup.HasCapFundamentalFormula C (completedIdentityClass C sX) fun _ ↦ 0 :=
  fun a ↦ ⟨by rw [completedIdentityClass_apply, DirectSum.of_eq_same], fun n ↦
    (BivariantClass.capFundamentalFormula_iff_of_heq C _ _ sX
      (congrFun (Scheme.Hom.connectedComponentsMap_id X) a)
      (Scheme.Hom.heq_of_comp_connectedComponentOpens_ι
        (congrFun (Scheme.Hom.connectedComponentsMap_id X) a) _ (𝟙 _)
        (by rw [Scheme.Hom.resConnectedComponent_comp_ι, Category.comp_id, Category.id_comp]; rfl))
      (completedIdentityClass_apply_heq C sX a) n).2
      (bivariantIdentityClassOfInvertible_capFundamentalFormula C _ n)⟩

/-! ### The Gysin class of a section of a smooth morphism -/

/-- A section of a morphism over a base is a morphism over that base. -/
theorem comp_structureMorphism_of_comp_eq_id {S X P : Scheme.{u}} {sX : X ⟶ S} {sP : P ⟶ S}
    {p : P ⟶ X} (hp : p ≫ sX = sP) {s : X ⟶ P} (hs : s ≫ p = 𝟙 X) : s ≫ sP = sX := by
  rw [← hp, ← Category.assoc, hs, Category.id_comp]

variable {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (p : P ⟶ X) [Smooth p]
  (hp : p ≫ sX = sP) (s : X ⟶ P) (hs : s ≫ p = 𝟙 X)

/-- Let `p : P ⟶ X` be a smooth morphism of schemes locally of finite type over the base and
`s : X ⟶ P` a section of `p`, a regular immersion by
`Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section`. Then

  `1 = s^! ∘ p^*` in `A^*(X)^∧`,

for `s^! = c(X ⟶ P, 𝒩_{X/P})` the class of Stacks 0FBQ (3) of the normal sheaf of `s` and `p^*`
the flat pullback of Stacks 0B78; the composite, a class for `s ≫ p`, is read as a class for
`𝟙 X = s ≫ p`. -/
@[stacks 0FF1 "second assertion: 1 = s^! ∘ p^* in A^*(X)^∧, the composite read as a completed \
class for 𝟙 X along s ≫ p = 𝟙 X"]
theorem completedBivariantCompositeOfInvertible_completedFlatPullbackOfSmooth_of_section :
    letI : IsImmersion s := Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id s p hs
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
    completedBivariantGroup.copy C hs
        (comp_comp_structureMorphism_eq (comp_structureMorphism_of_comp_eq_id hp hs) hp)
        (Category.id_comp sX)
        (completedBivariantCompositeOfInvertible C sX sP sX s p
          (comp_structureMorphism_of_comp_eq_id hp hs) hp
          (completedVirtualNormalGysinClassOfImmersion C sX sP s
            (comp_structureMorphism_of_comp_eq_id hp hs)
            (VirtualNormalBundle.ofIsRegularImmersion s
              (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section p s hs)))
          (completedFlatPullbackOfSmooth C sP sX p hp)) =
      completedIdentityClass C sX := by
  have : IsImmersion s := Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id s p hs
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have hreg := Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section p s hs
  have hsP := comp_structureMorphism_of_comp_eq_id hp hs
  have hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (Scheme.Hom.resConnectedComponent (𝟙 X) a) r :=
    fun a ↦ ⟨0, relativeDimension_of_isOpenImmersion _⟩
  have h0 : ∀ a, flatComponentRelativeDimension (𝟙 X) hrel a = 0 := fun a ↦
    flatComponentRelativeDimension_eq _ hrel a (relativeDimension_of_isOpenImmersion _)
  refine completedBivariantGroup.eq_of_hasCapFundamentalFormula C sX sX (𝟙 X)
    (Category.id_comp sX) hrel
    (((hasCapFundamentalFormula_completedVirtualNormalGysinClassOfOpen C sX sP s hsP _ _ _
      (VirtualNormalBundle.ofIsRegularImmersion s hreg)).comp_completedFlatPullbackOfSmooth C sX
        sP s hsP sX p hp).copy C hs _ _)
    (hasCapFundamentalFormula_completedIdentityClass C sX) (fun a ↦ ?_)
    fun a ↦ by rw [h0, Nat.cast_zero, neg_zero]
  obtain ⟨ξ, hξ, rfl⟩ := exists_mem_genericPoints_mk_eq a
  have hE := fiberRank_conormalModule_add_of_flat (f := 𝟙 X) s p hs hreg hξ
    (relativeDimension_of_isOpenImmersion _)
    (relativeDimension_smoothComponentRelativeDimension p _)
  have hrank : (componentRank ((VirtualNormalBundle.ofIsRegularImmersion s hreg).toOpenFactor
      s.liftCoborder_ι).bundle (_root_.ConnectedComponents.mk ξ) : ℤ) =
        Scheme.Modules.fiberRank (conormalModule s) ξ := by
    rw [← fiberRank_eq_componentRank _ _ ξ (mem_connectedComponentOpens_mk ξ)]
    exact congrArg _ (Scheme.Modules.fiberRank_dualSheaf (conormalModule s)
      (isFiniteLocallyFree_conormalModule s hreg) ξ)
  dsimp only
  rw [hrank, h0]
  lia

add_to_stacks 0FF1 "first assertion: a section s of a smooth morphism p is a regular immersion; \
it is Stacks 067R" Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section

end Stacks.Chow

end
