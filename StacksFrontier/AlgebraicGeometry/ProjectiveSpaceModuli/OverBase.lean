module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism `φ_{(L, (s₀, …, sₙ))}` to `ℙⁿ_S` and its characterisation

Let `S` be a scheme and `Y` a scheme over `S`, let `L` be an invertible `𝒪_Y`-module and let
`s₀, …, sₙ` be global sections of `L` generating it. Section 27.13 of the Stacks project
(Tag 01ND) writes

`φ_{(L, (s₀, …, sₙ))} : Y ⟶ ℙⁿ_S`

for the morphism over `S` combining the morphism `Y ⟶ ℙⁿ_ℤ` attached to the pair by Tag 01NE with
the structure morphism `Y ⟶ S`, and characterises it as the unique `S`-morphism such that
`L ≅ φ^* 𝒪_{ℙⁿ_S}(1)` and `sᵢ = φ^* Tᵢ`.

The morphism is `Stacks.ProjectiveFromSections.toProjectiveSpaceOver`. This file proves the
characterisation.

## Main definitions

* `Stacks.ProjectiveSpaceModuli.projectiveSpaceCoordSection`: the homogeneous coordinate `Tᵢ` as
  a global section of `𝒪_{ℙⁿ_S}(1)`.
* `Stacks.ProjectiveSpaceModuli.universalTupleOver`: the pair `(𝒪_{ℙⁿ_S}(1), (T₀, …, Tₙ))` on
  `ℙⁿ_S`.

## Main results

* `Stacks.ProjectiveSpaceModuli.eq_toProjectiveSpaceOver_iff`: **a morphism `g : Y ⟶ ℙⁿ_S` is
  `φ_{(L, (s₀, …, sₙ))}` if and only if it lies over `S` and there is an isomorphism
  `g^* 𝒪(1) ≅ L` carrying `g^* Tᵢ` to `sᵢ` for every `i`.**
* `Stacks.ProjectiveSpaceModuli.exists_iso_pullback_toProjectiveSpaceOver`: `φ^* 𝒪(1) ≅ L` with
  `φ^* Tᵢ ↦ sᵢ`.
* `Stacks.ProjectiveSpaceModuli.existsUnique_hom_projectiveSpaceOver`: the same characterisation
  as a unique-existence statement.

## Implementation notes

`ℙⁿ_S` is the fibre product `S ×_ℤ ℙⁿ_ℤ` (`AlgebraicGeometry.projectiveSpaceOver`, Tag 01NF), and
`𝒪_{ℙⁿ_S}(1)` is the pullback of `𝒪(1)` on `ℙⁿ_ℤ` along the projection
(`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`); the coordinate `Tᵢ` on `ℙⁿ_S`
is the pullback of the degree-one section `ψ(Tᵢ)` of `𝒪(1)` on `ℙⁿ_ℤ` (Tag 01NR). Under the
identification of `ℙⁿ_S` with the relative Proj of `𝒪_S[T₀, …, Tₙ]` of Tag 01O3, which is
compatible with the twisting sheaves, these are the sheaf and the sections the source refers to.

The proof reduces to the integral model: a morphism to the fibre product is determined by its two
projections, the pair pulled back along `g` is the tautological pair of `g` followed by the
projection (`Stacks.ProjectiveSpaceModuli.pointsOfHom_comp`), and the bijection of Tag 01NE
(`Stacks.ProjectiveSpaceModuli.pointsEquiv`) sends the class of `(L, s)` back to the glued morphism
`Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse`, which it pins on every chart.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections Stacks.TwistPullbackPinned

universe u

namespace Stacks.ProjectiveSpaceModuli

/-- **The homogeneous coordinate `Tᵢ` as a global section of `𝒪_{ℙⁿ_S}(1)`**: the pullback along
`ℙⁿ_S ⟶ ℙⁿ_ℤ` of the degree-one section `Tᵢ` of `𝒪(1)` on the integral model. -/
def projectiveSpaceCoordSection (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) :
    Γ(projectiveSpaceTwistingSheaf n S, ⊤) :=
  pullbackCoordSection.{u} (projectiveSpaceOver.toIntegralAtUniverse n S) i

/-- **The pair `(𝒪_{ℙⁿ_S}(1), (T₀, …, Tₙ))` on `ℙⁿ_S`**: the tautological pair of the projection
`ℙⁿ_S ⟶ ℙⁿ_ℤ`. -/
def universalTupleOver (n : ℕ) (S : Scheme.{u}) : GeneratingTuple (projectiveSpaceOver n S) n :=
  tautological (projectiveSpaceOver.toIntegralAtUniverse n S)

variable {X S : Scheme.{u}} {n : ℕ}

/-- The pair `(L, (s₀, …, sₙ))` as a `Stacks.ProjectiveSpaceModuli.GeneratingTuple`. -/
abbrev GeneratingTuple.mk' (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) : GeneratingTuple X n :=
  ⟨L, inferInstance, s, hs⟩

/-- **The pullback of `(𝒪_{ℙⁿ_S}(1), (T₀, …, Tₙ))` along `g` is identified with a pair `t`
exactly when `g` followed by the projection to `ℙⁿ_ℤ` is the morphism classifying `t`.** -/
theorem isomorphic_pullbackTuple_universalTupleOver_iff (t : GeneratingTuple X n)
    (g : X ⟶ projectiveSpaceOver n S) :
    Isomorphic (pullbackTuple g (universalTupleOver n S)) t ↔
      g ≫ projectiveSpaceOver.toIntegralAtUniverse n S = (pointsEquiv X n).symm ⟦t⟧ := by
  have h : pointsEquiv X n (g ≫ projectiveSpaceOver.toIntegralAtUniverse n S) =
      pullbackPoints g ⟦universalTupleOver n S⟧ :=
    pointsOfHom_comp g _
  rw [Equiv.eq_symm_apply, h, pullbackPoints_mk]
  exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)

/-- The morphism `X ⟶ ℙⁿ_ℤ` classifying `(L, (s₀, …, sₙ))` under the bijection of Tag 01NE is the
glued morphism `Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse`. -/
theorem pointsEquiv_symm_mk' :
    (pointsEquiv X n).symm ⟦GeneratingTuple.mk' L s hs⟧ = toProjectiveSpaceAtUniverse s hs :=
  pointsEquiv_symm_eq fun i => ι_toProjectiveSpaceAtUniverse s hs i

/-- **The characterisation of `φ_{(L, (s₀, …, sₙ))}` of Section 27.13.** For an `S`-scheme
`f : X ⟶ S`, an invertible `𝒪_X`-module `L` and global sections `s₀, …, sₙ` generating it, a
morphism `g : X ⟶ ℙⁿ_S` is `φ_{(L, (s₀, …, sₙ))}` if and only if `g` is a morphism over `S` and
there is an isomorphism `α : g^* 𝒪_{ℙⁿ_S}(1) ≅ L` with `α (g^* Tᵢ) = sᵢ` for `i = 0, …, n`. So
`φ_{(L, (s₀, …, sₙ))}` is the unique `S`-morphism with `L = φ^* 𝒪(1)` and `sᵢ = φ^* Tᵢ`. -/
@[stacks 01ND "phi_(L, (s_0, ..., s_n)) : Y -> P^n_S is the unique S-morphism with \
L = phi^* O_{P^n_S}(1) and s_i = phi^* T_i: a morphism g : Y -> P^n_S equals phi iff it lies \
over S and some isomorphism g^* O(1) = L carries g^* T_i to s_i for every i. The morphism is \
Stacks.ProjectiveFromSections.toProjectiveSpaceOver, P^n_S is Tag 01NF, O_{P^n_S}(1) and T_i \
are pulled back from P^n_Z"]
theorem eq_toProjectiveSpaceOver_iff (f : X ⟶ S) (g : X ⟶ projectiveSpaceOver n S) :
    g = toProjectiveSpaceOver s hs f ↔
      g ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        ∃ α : (Scheme.Modules.pullback g).obj (projectiveSpaceTwistingSheaf n S) ≅ L,
          ∀ i, Scheme.Modules.Hom.app α.hom ⊤
            (pullbackGlobalSections g (projectiveSpaceTwistingSheaf n S)
              (projectiveSpaceCoordSection n S i)) = s i := by
  have key : (∃ α : (Scheme.Modules.pullback g).obj (projectiveSpaceTwistingSheaf n S) ≅ L,
      ∀ i, Scheme.Modules.Hom.app α.hom ⊤
        (pullbackGlobalSections g (projectiveSpaceTwistingSheaf n S)
          (projectiveSpaceCoordSection n S i)) = s i) ↔
      g ≫ projectiveSpaceOver.toIntegralAtUniverse n S = toProjectiveSpaceAtUniverse s hs := by
    rw [← pointsEquiv_symm_mk' s hs]
    exact isomorphic_pullbackTuple_universalTupleOver_iff (GeneratingTuple.mk' L s hs) g
  rw [key]
  constructor
  · rintro rfl
    exact ⟨toProjectiveSpaceOver_fst s hs f, toProjectiveSpaceOver_snd s hs f⟩
  · rintro ⟨h₁, h₂⟩
    exact pullback.hom_ext (h₁.trans (toProjectiveSpaceOver_fst s hs f).symm)
      (h₂.trans (toProjectiveSpaceOver_snd s hs f).symm)

/-- **`φ_{(L, (s₀, …, sₙ))}^* 𝒪_{ℙⁿ_S}(1) ≅ L`, by an isomorphism carrying `φ^* Tᵢ` to `sᵢ`.** -/
theorem exists_iso_pullback_toProjectiveSpaceOver (f : X ⟶ S) :
    ∃ α : (Scheme.Modules.pullback (toProjectiveSpaceOver s hs f)).obj
        (projectiveSpaceTwistingSheaf n S) ≅ L,
      ∀ i, Scheme.Modules.Hom.app α.hom ⊤
        (pullbackGlobalSections (toProjectiveSpaceOver s hs f) (projectiveSpaceTwistingSheaf n S)
          (projectiveSpaceCoordSection n S i)) = s i :=
  ((eq_toProjectiveSpaceOver_iff s hs f _).mp rfl).2

include hs in
/-- **There is a unique `S`-morphism `g : X ⟶ ℙⁿ_S` with `L ≅ g^* 𝒪(1)` matching `sᵢ` with
`g^* Tᵢ`**, namely `φ_{(L, (s₀, …, sₙ))}`. -/
theorem existsUnique_hom_projectiveSpaceOver (f : X ⟶ S) :
    ∃! g : X ⟶ projectiveSpaceOver n S,
      g ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        ∃ α : (Scheme.Modules.pullback g).obj (projectiveSpaceTwistingSheaf n S) ≅ L,
          ∀ i, Scheme.Modules.Hom.app α.hom ⊤
            (pullbackGlobalSections g (projectiveSpaceTwistingSheaf n S)
              (projectiveSpaceCoordSection n S i)) = s i :=
  ⟨toProjectiveSpaceOver s hs f, (eq_toProjectiveSpaceOver_iff s hs f _).mp rfl,
    fun g hg => (eq_toProjectiveSpaceOver_iff s hs f g).mpr hg⟩

end Stacks.ProjectiveSpaceModuli

end
