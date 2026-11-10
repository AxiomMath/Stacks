module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemLifting
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemSections
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample

/-!
# An ample module gives an embedded generating tuple

For a proper morphism `f : X ⟶ S` and an ample invertible `𝒪_X`-module `L`, every sufficiently
large `d` admits a tuple of global sections of `L ^⊗ d` which generate it at every stalk and whose
attached morphism to `ℙᴺ_S` is a closed immersion over `S`.

## Main results

* `Stacks.AmpleFormalSystemEmbeddedTuple.app_hom_app_inv` — applying the inverse of an
  isomorphism of modules to a global section and then the isomorphism is the identity.
* `Stacks.AmpleFormalSystemEmbeddedTuple.transportTuple` — a generating tuple carried across an
  isomorphism of its underlying module, with the same attached morphism.
* `Stacks.AmpleFormalSystemEmbeddedTuple.isClosedImmersion_of_isImmersion_over` — an immersion
  into `ℙᴺ_S` over a proper morphism is a closed immersion.
* `Stacks.AmpleFormalSystemEmbeddedTuple.exists_generatingTuple_isClosedImmersion_of_isAmple` —
  for `f : X ⟶ S` proper and `L` ample there is a `d₀ ≥ 1` such that every `d ≥ d₀` admits
  `N + 1` generating global sections of `L ^⊗ d` whose attached morphism `X ⟶ ℙᴺ_S` over `S` is a
  closed immersion.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli
open Stacks.AmpleProjectiveImmersion Stacks.AmpleFormalSystemSections

universe u v

namespace Stacks.AmpleFormalSystemEmbeddedTuple

/-! ### Transporting a generating tuple across an isomorphism -/

/-- Applying the inverse of an isomorphism of modules to a global section and then the
isomorphism is the identity. -/
public lemma app_hom_app_inv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (y : Γ(N, ⊤)) :
    Scheme.Modules.Hom.app e.hom ⊤ (Scheme.Modules.Hom.app e.inv ⊤ y) = y := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply,
    show Scheme.Modules.Hom.app e.inv ⊤ ≫ Scheme.Modules.Hom.app e.hom ⊤ =
      Scheme.Modules.Hom.app (e.inv ≫ e.hom) ⊤ from rfl, e.inv_hom_id]
  simp

/-- **A generating tuple carried across an isomorphism of its underlying module.** -/
public def transportTuple {X : Scheme.{u}} {N : ℕ} (T : GeneratingTuple X N) {M : X.Modules}
    [IsInvertibleModule X M] (e : M ≅ T.bundle) : GeneratingTuple X N where
  bundle := M
  isInvertible := ‹_›
  coord k := Scheme.Modules.Hom.app e.inv ⊤ (T.coord k)
  generates :=
    Stacks.AmpleFormalSystemLifting.generatesStalks_congr e.symm T.coord T.generates

/-- The transported tuple is isomorphic to the original, hence has the same attached
morphism. -/
public lemma isomorphic_transportTuple {X : Scheme.{u}} {N : ℕ} (T : GeneratingTuple X N)
    {M : X.Modules} [IsInvertibleModule X M] (e : M ≅ T.bundle) :
    Isomorphic (transportTuple T e) T :=
  ⟨e, fun k => app_hom_app_inv e (T.coord k)⟩

/-! ### An immersion over a proper morphism is a closed immersion -/

/-- **An immersion into `ℙᴺ_S` lying over a proper morphism is a closed immersion.** -/
public lemma isClosedImmersion_of_isImmersion_over {X S : Scheme.{u}} {f : X ⟶ S} [IsProper f]
    {N : ℕ} (ψ : X ⟶ projectiveSpaceOver N S) (hψ : IsImmersion ψ)
    (hover : ψ ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} N)) = f) :
    IsClosedImmersion ψ := by
  have := hψ
  have hover' : ψ ≫ (projectiveSpaceOver N S ↘ S) = f := hover
  have : IsProper (projectiveSpaceOver N S ↘ S) := isProper_projectiveSpaceOver N S
  have : UniversallyClosed (ψ ≫ (projectiveSpaceOver N S ↘ S)) := by
    rw [hover']; infer_instance
  have : UniversallyClosed ψ :=
    UniversallyClosed.of_comp_of_isSeparated ψ (projectiveSpaceOver N S ↘ S)
  exact IsClosedImmersion.of_isPreimmersion ψ ψ.isClosedMap.isClosed_range

/-! ### The embedding step with its sections -/

/-- Let `f : X ⟶ S` be proper and `L` an ample invertible `𝒪_X`-module. Then there is a `d₀ ≥ 1`
such that for every `d ≥ d₀` there are an `N` and `N + 1` global sections of `L ^⊗ d` which
generate it at every stalk and whose attached morphism `X ⟶ ℙᴺ_S` over `S` is a closed immersion.
-/
public theorem exists_generatingTuple_isClosedImmersion_of_isAmple {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (N : ℕ) (s : Fin (N + 1) → Γ(tensorPowModule X L (d : ℤ), ⊤))
        (hs : GeneratesStalks s),
        IsClosedImmersion (liftOver f (tupleHom
          (⟨tensorPowModule X L (d : ℤ), inferInstance, s, hs⟩ : GeneratingTuple X N))) := by
  obtain ⟨d₀, hd₀, hd⟩ :=
    Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple f L hL
  refine ⟨d₀, hd₀, fun d hdd => ?_⟩
  obtain ⟨N, ψ, hψ, hover, ⟨e⟩⟩ := hd d hdd
  set g : X ⟶ projectiveSpaceAtUniverse.{u} N :=
    ψ ≫ projectiveSpaceOver.toIntegralAtUniverse N S with hg
  set β : tensorPowModule X L (d : ℤ) ≅ (tautological g).bundle :=
    e ≪≫ (Scheme.Modules.pullbackComp ψ
      (projectiveSpaceOver.toIntegralAtUniverse N S)).app (twistingSheafAtUniverse.{u} N)
  refine ⟨N, (transportTuple (tautological g) β).coord,
    (transportTuple (tautological g) β).generates, ?_⟩
  change IsClosedImmersion (liftOver f (tupleHom (transportTuple (tautological g) β)))
  rw [tupleHom_congr (isomorphic_transportTuple (tautological g) β), tupleHom_tautological, hg,
    liftOver_eq f ψ hover]
  exact isClosedImmersion_of_isImmersion_over (f := f) ψ hψ hover

end Stacks.AmpleFormalSystemEmbeddedTuple

end
