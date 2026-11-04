module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ColimitSectionsQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerColimitCocone

/-!
# The colimit assertion of Tag 0EBN reduced to quasi-compact opens

`AlgebraicGeometry.CoherentReflexive.reflexivePowerCocone` is the cocone

`𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯ ⟶ j_*𝒪_U`

of [Stacks, Tag 0EBN], and what the tag asserts is that it is a colimit.  This file reduces that
assertion to the statement the source actually proves, namely that for every quasi-compact open
`W ⊆ X` the comparison

`colim_n Γ(W, ℱ^{[n]}) ⟶ Γ(W, j_*𝒪_U) = Γ(U ∩ W, 𝒪_U)`

is bijective, written out as two elementary conditions on the legs of the cocone: joint
surjectivity on sections over `W`, and the vanishing of a section killed by a leg under some
multiplication by a power of `σ`.

The reduction itself is `AlgebraicGeometry.isColimitOfForallIsCompact` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/ColimitSectionsQuasiCompact.lean`; this file
instantiates it at the cocone of reflexive powers, and at the open `U` of the tag.  It also
records that the trivializations the cocone is built from are isomorphisms, which is what makes
the two conditions statements about restricting a section to `U ∩ W` and multiplying by a power
of `σ`.

## Main definitions

* `AlgebraicGeometry.CoherentReflexive.reflexivePowerRestrictLegIso`: the trivialization
  `ℱ^{[n]}|_U ≅ 𝒪_U` out of which the `n`-th leg is built.
* `AlgebraicGeometry.CoherentReflexive.isColimitReflexivePowerCoconeOfForallIsCompact`: **the
  cocone is a colimit** given the two per-quasi-compact-open conditions.
* `AlgebraicGeometry.CoherentReflexive.isColimitSectionIsomorphismOpenCoconeOfForallIsCompact`:
  the same on the open `U` of [Stacks, Tag 0EBN] attached to a global section.

## Main results

* `Stacks.CategoryTheory.isIso_invSeqLeg`: the morphisms obtained by inverting a sequence of
  isomorphisms are isomorphisms.
* `AlgebraicGeometry.CoherentReflexive.isIso_reflexivePowerRestrictLeg`: **each trivialization
  `ℱ^{[n]}|_U ⟶ 𝒪_U` of the cocone is an isomorphism.**

## Implementation notes

**How the two hypotheses are discharged.**  The two hypotheses of
`isColimitSectionIsomorphismOpenCoconeOfForallIsCompact` are the content of the source's argument
with the open `V`.  They are proved, over affine opens, in
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/ReflexivePowerColimit.lean`, where the colimit
assertion of [Stacks, Tag 0EBN] is concluded; the passage from a basis of opens to the sheaf
statement, and the compatibility with restriction maps that the source explicitly omits, are the
ones discharged above.

**Why the trivializations are isomorphisms.**  They are defined by inverting the restricted
multiplication maps and composing down to degree zero
(`Stacks.CategoryTheory.invSeqLeg`), where the morphism is the isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`; so the whole composite is invertible by
induction.  This matters because it is what turns "the `n`-th leg kills `η`" into "`η` restricted
to `U ∩ W` is zero", with no reference to the inverse maps.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (unitModule)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules inclusion)

universe u v₁ u₁

namespace Stacks.CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- **The morphisms of `Stacks.CategoryTheory.invSeqLeg` are isomorphisms** as soon as the
morphism out of the first term is one: each is a composite of inverses of the transition maps
with it. -/
theorem isIso_invSeqLeg {Z : ℕ → C} (f : ∀ n, Z n ⟶ Z (n + 1)) (hf : ∀ n, IsIso (f n)) {Q : C}
    (t : Z 0 ⟶ Q) (ht : IsIso t) (n : ℕ) : IsIso (invSeqLeg f hf t n) := by
  induction n with
  | zero => exact ht
  | succ n ih =>
    rw [invSeqLeg_succ]
    have := ih
    infer_instance

end Stacks.CategoryTheory

namespace AlgebraicGeometry.CoherentReflexive

open Stacks.CategoryTheory (invSeqLeg isIso_invSeqLeg)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
  (F : CoherentReflexiveModules X) (σ : unitObj X ⟶ F)
  (hstep : ∀ n : ℕ, IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    (reflexivePowerStep F σ n).hom.hom))

/-- **The trivializations `ℱ^{[n]}|_U ⟶ 𝒪_U` of the cocone of [Stacks, Tag 0EBN] are
isomorphisms.**  In degree zero the trivialization is
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, and each further one is obtained by
inverting the restricted multiplication map, so all of them are invertible. -/
theorem isIso_reflexivePowerRestrictLeg (n : ℕ) :
    IsIso (reflexivePowerRestrictLeg U F σ hstep n) :=
  isIso_invSeqLeg _ hstep _ (Iso.isIso_hom (Scheme.Modules.restrictUnitIso U.ι)) n

/-- **The trivialization `ℱ^{[n]}|_U ≅ 𝒪_U`**, compatible with multiplication by `σ` by
`AlgebraicGeometry.CoherentReflexive.reflexivePowerStep_comp_reflexivePowerRestrictLeg`. -/
def reflexivePowerRestrictLegIso (n : ℕ) :
    Scheme.Modules.restrict (reflexivePower F n).obj.obj U.ι ≅ unitModule U.toScheme :=
  @asIso _ _ _ _ _ (isIso_reflexivePowerRestrictLeg U F σ hstep n)

/-- The forward map of `reflexivePowerRestrictLegIso` is the trivialization
`reflexivePowerRestrictLeg`. -/
@[simp] theorem reflexivePowerRestrictLegIso_hom (n : ℕ) :
    (reflexivePowerRestrictLegIso U F σ hstep n).hom
      = reflexivePowerRestrictLeg U F σ hstep n := rfl

/-! ### The adjoint of a trivialization on sections -/

section Adjunction

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]

/-- **The adjoint of a morphism `𝒜|_Y ⟶ ℬ` acts on sections over an open `W` of `Z` by
restricting to the image of `f ⁻¹ᵁ W` and then applying the morphism.**  The unit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is a restriction map of `𝒜`, by
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`, and the pushforward of a
morphism acts on sections over `W` as the morphism acts over `f ⁻¹ᵁ W`. -/
theorem restrictAdjunction_homEquiv_app_apply (A : Z.Modules) (B : Y.Modules)
    (g : Scheme.Modules.restrict A f ⟶ B) (W : Z.Opens) (η : Γ(A, W)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).homEquiv A B g) W η
      = Scheme.Modules.Hom.app g (f ⁻¹ᵁ W)
          (A.presheaf.map (homOfLE (f.image_preimage_le W)).op η) := by
  rw [Adjunction.homEquiv_unit]
  rfl

end Adjunction

/-! ### Sections through an isomorphism -/

/-- An isomorphism of `𝒪_X`-modules is a bijection on sections over every open, read as the
equivalence of the two ways of writing one section in terms of the other. -/
theorem app_hom_eq_iff_eq_app_inv {Z : Scheme.{u}} {A B : Z.Modules} (e : A ≅ B) (W : Z.Opens)
    (a : Γ(A, W)) (b : Γ(B, W)) :
    Scheme.Modules.Hom.app e.hom W a = b ↔ a = Scheme.Modules.Hom.app e.inv W b := by
  have key : ∀ {A B : Z.Modules} (e : A ≅ B) (c : Γ(A, W)),
      Scheme.Modules.Hom.app e.inv W (Scheme.Modules.Hom.app e.hom W c) = c := by
    intro A B e c
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, key]
  · rw [h]
    exact key e.symm b

/-! ### The colimit criterion for the cocone of reflexive powers -/

/-- **The cocone `ℱ^{[n]} ⟶ j_*𝒪_U` of [Stacks, Tag 0EBN] is a colimit** as soon as, over every
quasi-compact open `W ⊆ X`, its legs are jointly surjective on sections and kill only sections
that some multiplication by a power of `σ` kills.

These two conditions are exactly the bijectivity of
`colim_n Γ(W, ℱ^{[n]}) ⟶ Γ(W, j_*𝒪_U) = Γ(U ∩ W, 𝒪_U)`, which is the statement the source
proves by choosing an open `V` with `ℱ|_V` invertible whose complement has codimension at least
two and applying [Stacks, Tag 01PW] (2) on `V ∩ W`.  Everything between that statement and the
colimit assertion — the passage from quasi-compact opens to all of `X`, and the compatibility of
the comparison with the restriction maps, which the source omits — is discharged by
`AlgebraicGeometry.isColimitOfForallIsCompact`. -/
def isColimitReflexivePowerCoconeOfForallIsCompact
    (hsurj : ∀ W : X.Opens, IsCompact (W : Set X) →
      ∀ ξ : Γ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme), W),
        ∃ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W)),
          Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) W η = ξ)
    (hker : ∀ W : X.Opens, IsCompact (W : Set X) →
      ∀ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W)),
        Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) W η = 0 →
          ∃ (m : ℕ) (h : n ≤ m),
            Scheme.Modules.Hom.app ((reflexivePowerModules F σ).map (homOfLE h)) W η = 0) :
    IsColimit (reflexivePowerCocone U F σ hstep) :=
  isColimitOfForallIsCompact (reflexivePowerCocone U F σ hstep)
    (fun W hW ξ => hsurj W hW ξ) fun W hW n η h => hker W hW n η h

/-- **The `n`-th leg of the cocone acts on sections by restricting to `U ∩ W` and applying the
trivialization `ℱ^{[n]}|_U ≅ 𝒪_U`.** -/
theorem reflexivePowerPushforwardLeg_app (n : ℕ) (W : X.Opens)
    (η : Γ((reflexivePower F n).obj.obj, W)) :
    Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) W η
      = Scheme.Modules.Hom.app (reflexivePowerRestrictLeg U F σ hstep n) (U.ι ⁻¹ᵁ W)
          ((Scheme.Modules.presheaf (reflexivePower F n).obj.obj).map
            (homOfLE (U.ι.image_preimage_le W)).op η) :=
  restrictAdjunction_homEquiv_app_apply U.ι _ _ _ W η

/-- **The cocone `ℱ^{[n]} ⟶ j_*𝒪_U` of [Stacks, Tag 0EBN] is a colimit** as soon as, over every
quasi-compact open `W ⊆ X`:

* every section of `𝒪_U` over `U ∩ W` is, for some `n`, the image under the trivialization
  `𝒪_U ≅ ℱ^{[n]}|_U` of the restriction of a section of `ℱ^{[n]}` over `W` — in the source's
  language, `sⁿ ξ` extends from `U ∩ W` to `W`;
* a section of `ℱ^{[n]}` over `W` whose restriction to `U ∩ W` vanishes is killed by some
  multiplication by a power of `σ`.

This is the form in which the source's argument with the open `V` proves the two conditions of
`isColimitReflexivePowerCoconeOfForallIsCompact`: the trivializations are isomorphisms, so the
`n`-th leg vanishes on a section exactly when the section vanishes on `U ∩ W`. -/
def isColimitReflexivePowerCoconeOfForallIsCompactRestrict
    (hsurj : ∀ W : X.Opens, IsCompact (W : Set X) →
      ∀ ξ : Γ(unitModule U.toScheme, U.ι ⁻¹ᵁ W),
        ∃ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W)),
          (Scheme.Modules.presheaf (reflexivePower F n).obj.obj).map
              (homOfLE (U.ι.image_preimage_le W)).op η
            = Scheme.Modules.Hom.app (reflexivePowerRestrictLegIso U F σ hstep n).inv
                (U.ι ⁻¹ᵁ W) ξ)
    (hker : ∀ W : X.Opens, IsCompact (W : Set X) →
      ∀ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W)),
        (Scheme.Modules.presheaf (reflexivePower F n).obj.obj).map
            (homOfLE (U.ι.image_preimage_le W)).op η = 0 →
          ∃ (m : ℕ) (h : n ≤ m),
            Scheme.Modules.Hom.app ((reflexivePowerModules F σ).map (homOfLE h)) W η = 0) :
    IsColimit (reflexivePowerCocone U F σ hstep) := by
  refine isColimitReflexivePowerCoconeOfForallIsCompact U F σ hstep (fun W hW ξ => ?_)
    (fun W hW n η h => ?_)
  · obtain ⟨n, η, hη⟩ := hsurj W hW ξ
    refine ⟨n, η, ?_⟩
    rw [reflexivePowerPushforwardLeg_app]
    exact (app_hom_eq_iff_eq_app_inv (reflexivePowerRestrictLegIso U F σ hstep n)
      (U.ι ⁻¹ᵁ W) _ ξ).2 hη
  · refine hker W hW n η ?_
    rw [reflexivePowerPushforwardLeg_app] at h
    have hz := (app_hom_eq_iff_eq_app_inv (reflexivePowerRestrictLegIso U F σ hstep n)
      (U.ι ⁻¹ᵁ W) _ 0).1 h
    rw [hz, map_zero]
    rfl

variable [IsNormal X] [_root_.SheafOfModules.IsCoherent F.obj.obj]

/-- **The colimit assertion of [Stacks, Tag 0EBN] reduced to quasi-compact opens**, on the open
`U` of the tag itself: the cocone `ℱ^{[n]} ⟶ j_*𝒪_U` attached to a global section `s` of a
coherent reflexive module is a colimit as soon as, over every quasi-compact open `W`, its legs
are jointly surjective on sections and kill only sections killed by a power of `s`. -/
def isColimitSectionIsomorphismOpenCoconeOfForallIsCompact (s : F.obj.obj.sections)
    (hsurj : ∀ W : X.Opens, IsCompact (W : Set X) →
      ∀ ξ : Γ((Scheme.Modules.pushforward (sectionIsomorphismOpen X F.obj.obj s).ι).obj
          (unitModule (sectionIsomorphismOpen X F.obj.obj s).toScheme), W),
        ∃ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W)),
          Scheme.Modules.Hom.app
            (reflexivePowerPushforwardLeg (sectionIsomorphismOpen X F.obj.obj s) F
              (sectionObjHom F s)
              (isIso_restrict_reflexivePowerStep_sectionIsomorphismOpen F s) n) W η = ξ)
    (hker : ∀ W : X.Opens, IsCompact (W : Set X) →
      ∀ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W)),
        Scheme.Modules.Hom.app
            (reflexivePowerPushforwardLeg (sectionIsomorphismOpen X F.obj.obj s) F
              (sectionObjHom F s)
              (isIso_restrict_reflexivePowerStep_sectionIsomorphismOpen F s) n) W η = 0 →
          ∃ (m : ℕ) (h : n ≤ m),
            Scheme.Modules.Hom.app
              ((reflexivePowerModules F (sectionObjHom F s)).map (homOfLE h)) W η = 0) :
    IsColimit (sectionIsomorphismOpenCocone F s) :=
  isColimitReflexivePowerCoconeOfForallIsCompact _ F _ _ hsurj hker

end AlgebraicGeometry.CoherentReflexive

end
