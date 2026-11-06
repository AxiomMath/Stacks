module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovedLiftConormal

/-!
# The action `θ · c` of local derivations is a simply transitive action

Let `Z ⊂ X` and `W₀ ⊂ W` be first order thickenings of algebraic spaces over a base `T`, and fix
`e₀ : Z ⟶ W₀`.  For a morphism of thickenings `(e₀, c)` over `T` and an `𝒪_Z`-linear map
`θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}`, the morphism `θ · c` of [Stacks Project, Tag 0CK6] is
`AlgebraicGeometry.Space.derivationMove`.  This file proves the two facts that make
`(θ, c) ↦ θ · c` an action of the group `Hom(e₀^*Ω_{W₀/T}, 𝒞_{Z/X})` on the set of morphisms
`(e₀, c)` over `T` with a fixed map of conormal modules, and that the action is simply transitive
there — the sectionwise content of [Stacks Project, Tag 061C], which the source proves as "a
combination of Lemmas 0618, 04D0 and 061A":

* `AlgebraicGeometry.Space.derivationMove_zero` and `AlgebraicGeometry.Space.derivationMove_add`:
  `0 · c = c` and `(θ₁ + θ₂) · c = θ₁ · (θ₂ · c)`, from the uniqueness of [Stacks Project,
  Tag 04D0] and the additivity of the derivation `D = d_{W₀/T} ∘ θ` of Equation 0619 in `θ`;
* `AlgebraicGeometry.Space.exists_derivationMove_eq`: transitivity, from
  [Stacks Project, Tag 0618] and the surjectivity of Equation 0619;
* `AlgebraicGeometry.Space.derivationMove_injective`: freeness, from the injectivity of
  Equation 0619 and the local surjectivity of `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`.

## References

* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

section Additivity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y T X : AlgebraicSpaces B S hS} (b : Y ⟶ T) (a : X ⟶ Y) (C : Modules B S hS X.1 X.2)

/-- The derivation attached to `θ` by Equation [Stacks Project, Tag 0619] is additive in `θ`. -/
theorem derivationFamilyOfHom_add
    (θ₁ θ₂ : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ C)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) (t : (structureRingSheaf B S hS Y).obj.obj V) :
    derivationFamilyOfHom B S hS b a C (θ₁ + θ₂) V t =
      derivationFamilyOfHom B S hS b a C θ₁ V t + derivationFamilyOfHom B S hS b a C θ₂ V t :=
  congrArg (fun m : sheafOfDifferentials B S hS b ⟶ (modulePushforward B S hS a).obj C =>
      (m.val.app V).hom ((universalDerivation B S hS b).d t))
    (map_add ((modulePullbackAdjunction B S hS a).homAddEquiv
      (sheafOfDifferentials B S hS b) C) θ₁ θ₂)

/-- The derivation attached to `θ = 0` by Equation [Stacks Project, Tag 0619] is zero. -/
theorem derivationFamilyOfHom_zero (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (t : (structureRingSheaf B S hS Y).obj.obj V) :
    derivationFamilyOfHom B S hS b a C 0 V t = 0 :=
  congrArg (fun m : sheafOfDifferentials B S hS b ⟶ (modulePushforward B S hS a).obj C =>
      (m.val.app V).hom ((universalDerivation B S hS b).d t))
    (map_zero ((modulePullbackAdjunction B S hS a).homAddEquiv
      (sheafOfDifferentials B S hS b) C))

end Additivity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (q : W ⟶ T)

/-- **Equation [Stacks Project, Tag 0619] is injective on the values at `j^♯`.**  Two maps
`θ, θ' : e₀^*Ω_{W₀/T} ⟶ C` whose derivations agree on every section in the image of the locally
surjective `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}` are equal: the derivations agree on a covering of every
section, so everywhere, the module of values being a sheaf; and Equation 0619 is a bijection. -/
theorem eq_of_derivationFamilyOfHom_structureSharpRingInverseImage_eq
    (C : Modules B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).2)
    (θ θ' : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶ C)
    (h : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
      derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀ C θ V
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x) =
        derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀ C θ' V
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x)) :
    θ = θ' := by
  apply (derivationDirectImageEquiv B S hS e₀ (subspaceInclusion B S hS W W₀ ≫ q) C).injective
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext V t
  refine ((modulePushforward B S hS e₀).obj C).isSheaf.isSeparated V.unop _
    ((isLocallySurjective_structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W W₀) W₀.2.2).imageSieve_mem t) _ _ ?_
  intro Y p hp
  obtain ⟨y, hy⟩ := hp
  have key := fun φ ↦ (congrArg (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q)
    e₀ C φ (op Y)) hy).trans (derivationFamilyOfHom_map B S hS
      (subspaceInclusion B S hS W W₀ ≫ q) e₀ C φ V (op Y) p.op t)
  exact (key θ).symm.trans ((h (op Y) y).trans (key θ'))

variable (hZ : IsFirstOrderThickening B S hS X Z.1) (hW : IsFirstOrderThickening B S hS W W₀.1)
  (c : X ⟶ W) (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (p : X ⟶ T) (hcq : c ≫ q = p)

/-- The transported comorphism depends only on the morphism, not on the proof that it restricts
to `e₀ ≫ j`. -/
theorem restrictedSharpThroughThickening_congr {c c' : X ⟶ W} (h : c = c')
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc =
      restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc' := by
  subst h
  rfl

include hW in
/-- **`0 · c = c`.** -/
theorem derivationMove_zero :
    derivationMove B S hS Z W₀ e₀ q hZ c hc 0 p hcq = c := by
  refine (eq_derivationMove B S hS Z W₀ e₀ q hZ hW c hc 0 p hcq c
    ⟨hc, hcq, rfl, fun V x ↦ ?_⟩).symm
  refine (congrArg (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
    (derivationFamilyOfHom_zero B S hS _ e₀ _ V _)).trans ?_
  exact (map_zero _).trans (sub_self _).symm

include hW in
/-- **`(θ₁ + θ₂) · c = θ₁ · (θ₂ · c)`.**  The two facts `hc₂` and `hcq₂` about `θ₂ · c` that the
outer action needs are the first two clauses of `AlgebraicGeometry.Space.derivationMove_spec`;
they are taken as arguments so that the statement names no proof term. -/
theorem derivationMove_add
    (θ₁ θ₂ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (hc₂ : subspaceInclusion B S hS X Z ≫ derivationMove B S hS Z W₀ e₀ q hZ c hc θ₂ p hcq =
      e₀ ≫ subspaceInclusion B S hS W W₀)
    (hcq₂ : derivationMove B S hS Z W₀ e₀ q hZ c hc θ₂ p hcq ≫ q = p) :
    derivationMove B S hS Z W₀ e₀ q hZ c hc (θ₁ + θ₂) p hcq =
      derivationMove B S hS Z W₀ e₀ q hZ (derivationMove B S hS Z W₀ e₀ q hZ c hc θ₂ p hcq)
        hc₂ θ₁ p hcq₂ := by
  have hs₂ := derivationMove_spec B S hS Z W₀ e₀ q hZ hW c hc θ₂ p hcq
  have hs₁₂ := derivationMove_spec B S hS Z W₀ e₀ q hZ hW
    (derivationMove B S hS Z W₀ e₀ q hZ c hc θ₂ p hcq) hc₂ θ₁ p hcq₂
  obtain ⟨hb₂, -, hcon₂, hD₂⟩ := hs₂
  obtain ⟨hb₁₂, hbq₁₂, hcon₁₂, hD₁₂⟩ := hs₁₂
  refine (eq_derivationMove B S hS Z W₀ e₀ q hZ hW c hc (θ₁ + θ₂) p hcq _
    ⟨hb₁₂, hbq₁₂, hcon₂.trans hcon₁₂, fun V x ↦ ?_⟩).symm
  refine (congrArg (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
    (derivationFamilyOfHom_add B S hS _ e₀ _ θ₁ θ₂ V _)).trans ?_
  rw [map_add, hD₁₂ V x, hD₂ V x]
  exact sub_add_sub_cancel' _ _ _

include hW in
/-- **Transitivity.**  Two morphisms of first order thickenings `(e₀, c), (e₀, c')` over `T` with
the same map of conormal modules differ by the action of some `θ`: [Stacks Project, Tag 0618]
provides the derivation `D` with `c^♯ − (c')^♯ = ι ∘ D ∘ j^♯`, and Equation 0619 the `θ` with
`D = d_{W₀/T} ∘ θ`. -/
theorem exists_derivationMove_eq (c' : X ⟶ W)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hcq' : c' ≫ q = p)
    (hcon : conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ c' e₀ hc') :
    ∃ θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z,
      derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq = c' := by
  obtain ⟨D, hD⟩ := exists_derivation_of_conormalMap_eq B S hS Z W₀ e₀ q hZ hW c c' hc hc' p hcq
    hcq' hcon
  obtain ⟨θ, rfl⟩ := (derivationDirectImageEquiv B S hS e₀ (subspaceInclusion B S hS W W₀ ≫ q)
    (conormalModule B S hS X Z)).surjective D
  exact ⟨θ, (eq_derivationMove B S hS Z W₀ e₀ q hZ hW c hc θ p hcq c' ⟨hc', hcq', hcon, hD⟩).symm⟩

include hW in
/-- **Freeness.**  If `θ · c = θ' · c` then `θ = θ'`: the two derivations agree on the image of
`j^♯`, the inclusion `ι` of the square-zero ideal being injective. -/
theorem derivationMove_injective
    (θ θ' : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (h : derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq =
      derivationMove B S hS Z W₀ e₀ q hZ c hc θ' p hcq) :
    θ = θ' := by
  obtain ⟨hb, -, -, hD⟩ := derivationMove_spec B S hS Z W₀ e₀ q hZ hW c hc θ p hcq
  obtain ⟨hb', -, -, hD'⟩ := derivationMove_spec B S hS Z W₀ e₀ q hZ hW c hc θ' p hcq
  refine eq_of_derivationFamilyOfHom_structureSharpRingInverseImage_eq B S hS Z W₀ e₀ q _ θ θ'
    fun V x ↦ (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι_injective ?_
  rw [hD V x, hD' V x, restrictedSharpThroughThickening_congr B S hS Z W₀ e₀ h hb hb']

end AlgebraicGeometry.Space

end
