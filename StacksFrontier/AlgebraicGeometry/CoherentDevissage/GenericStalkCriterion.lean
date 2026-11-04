module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IrreducibleSupportCriterion
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport

/-!
# Devissage of coherent modules from one generic test object per integral closed subscheme

[Stacks, Tag 01YI]: a property `P` of coherent modules on a Noetherian scheme `X` which
satisfies the two-out-of-three condition in short exact sequences, and for which every integral
closed subscheme `Z ⊆ X` with generic point `ξ` carries some coherent module `𝒢` with
`Supp 𝒢 = Z`, with `𝒢_ξ` killed by `𝔪_ξ` and of length one there, and with `P 𝒢`, holds on
every coherent module. The proof is by Noetherian induction over `TopologicalSpace.Closeds X`,
through [Stacks, Tag 01YH] and [Stacks, Tag 01YG].

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_generic_stalk`: the
  criterion with `P` on the zero module assumed.
* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_generic_stalk_of_nonempty`:
  **[Stacks, Tag 01YI]**, on a nonempty scheme, with nothing assumed about the zero module.

## Implementation notes

The statement of [Stacks, Tag 01YI] fails on the empty scheme: on `Spec` of the zero ring there
is no integral closed subscheme, so both hypotheses hold for `P := fun _ => False`, while the
zero module is coherent and fails `P`. The tagged form therefore assumes `X` nonempty, and on a
nonempty `X` the test object for the closure of a point gives `P` on the zero module by
two-out-of-three applied to `0 → 𝒢 → 𝒢 → 0 → 0`. The variant
`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_generic_stalk` assumes
`P (⊤_ X.Modules)` instead and applies to every Noetherian scheme.

Coherence is spelled `_root_.SheafOfModules.IsCoherent`: inside the `Stacks.` namespace an
unqualified spelling can resolve to `Stacks.SheafOfModules.IsCoherent`, a different predicate.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

/-- The image of the generic point of an integral closed subscheme is generic in its range. -/
private theorem isGenericPoint_genericPoint_range {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] :
    IsGenericPoint (i (genericPoint Z)) (Set.range i.base) := by
  have h := (genericPoint_spec Z).image i.continuous
  rwa [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h

/-- The direct image of a sheaf of ideals along a closed immersion is supported on its range. -/
private theorem supp_pushforward_subset_range {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule) :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) ⊆
      Set.range i.base := by
  rw [_root_.AlgebraicGeometry.supp_pushforward_of_isClosedImmersion i I.toSheafOfModules]
  exact Set.image_subset_range _ _

/-- **The Noetherian induction of [Stacks, Tag 01YI].** For every irreducible closed subset `T`
of `X`, the property holds on every coherent module supported inside `T`. -/
private theorem property_of_supp_subset_of_generic_stalk
    (X : Scheme.{u}) [IsNoetherian X] (P : X.Modules → Prop)
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hgeneric : ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ ξ : X, IsGenericPoint ξ (Set.range i.base) →
      ∃ G : X.Modules, _root_.SheafOfModules.IsCoherent G ∧
        SheafOfModules.supp G = Set.range i.base ∧
        Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
        (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val ξ
         Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
        P G) :
    ∀ T : TopologicalSpace.Closeds X, IsIrreducible (T : Set X) →
      ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F →
        SheafOfModules.supp F ⊆ (T : Set X) → P F := by
  intro T
  refine (wellFounded_lt : WellFounded ((· < ·) :
    TopologicalSpace.Closeds X → TopologicalSpace.Closeds X → Prop)).induction
      (C := fun T => IsIrreducible (T : Set X) → ∀ F : X.Modules,
        _root_.SheafOfModules.IsCoherent F →
        SheafOfModules.supp F ⊆ (T : Set X) → P F) T ?_
  intro T ih hT
  obtain ⟨W, i, hci, hint, hrange⟩ :=
    IrreducibleDevissage.exists_isIntegral_isClosedImmersion_range_eq T hT
  have : IsClosedImmersion i := hci
  have : IsIntegral W := hint
  have hηgen : IsGenericPoint (i (genericPoint W)) (T : Set X) := by
    simpa [hrange] using isGenericPoint_genericPoint_range i
  refine IrreducibleSupportDevissage.property_of_irreducible_support X (T : Set X)
    T.isClosed hT (i (genericPoint W)) hηgen P hexact ?_ ?_
  · intro Z' i' hci' hint' hlt I hI
    have hclosed' : IsClosed (Set.range i'.base) := i'.isClosedEmbedding.isClosed_range
    exact ih ⟨Set.range i'.base, hclosed'⟩ hlt (isGenericPoint_genericPoint_range i').isIrreducible
      _ (IrreducibleSupportDevissage.coherent_pushforward_ideal i' I)
      (supp_pushforward_subset_range i' I)
  · obtain ⟨G, hGc, hGs, hGann, hGlen, hGP⟩ :=
      hgeneric W i hci hint (i (genericPoint W)) (by rw [hrange]; exact hηgen)
    exact ⟨G, hGc, hGs.trans hrange, hGann, hGlen, hGP⟩

/-- **[Stacks, Tag 01YI] with the zero module assumed.** Let `X` be a Noetherian scheme and let
`P` be a property of coherent `𝒪_X`-modules which holds on the zero module, satisfies the
two-out-of-three condition in short exact sequences of coherent modules, and for which every
integral closed subscheme `i : Z ⟶ X` with generic point `ξ` carries a coherent module `𝒢` with
support the range of `i`, with `𝒢_ξ` killed by the maximal ideal and of length one over the
local ring at `ξ`, and with `P 𝒢`. Then `P` holds on every coherent `𝒪_X`-module. -/
public theorem property_of_isCoherent_of_generic_stalk
    (X : Scheme.{u}) [IsNoetherian X] (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hgeneric : ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ ξ : X, IsGenericPoint ξ (Set.range i.base) →
      ∃ G : X.Modules, _root_.SheafOfModules.IsCoherent G ∧
        SheafOfModules.supp G = Set.range i.base ∧
        Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
        (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val ξ
         Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
        P G) :
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → P F := by
  refine property_of_isCoherent X P hzero
    (fun S hS h1 h2 h3 hp1 hp3 => (hexact S hS h1 h2 h3).2.1 ⟨hp1, hp3⟩) ?_
  intro Z i hci hint I hI
  have : I.toSheafOfModules.IsQuasicoherent := hI
  have hclosed : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  exact property_of_supp_subset_of_generic_stalk X P hexact hgeneric
    ⟨Set.range i.base, hclosed⟩ (isGenericPoint_genericPoint_range i).isIrreducible _
    (IrreducibleSupportDevissage.coherent_pushforward_ideal i I)
    (supp_pushforward_subset_range i I)

/-- **[Stacks, Tag 01YI].** Let `X` be a nonempty Noetherian scheme and let `P` be a property of
coherent `𝒪_X`-modules such that

1. for a short exact sequence of coherent modules, if two out of three have `P` then so does the
   third, and
2. every integral closed subscheme `i : Z ⟶ X` with generic point `ξ` carries some coherent
   module `𝒢` with `Supp 𝒢` the range of `i`, with `𝒢_ξ` annihilated by `𝔪_ξ` and of length one
   over `𝒪_{X,ξ}`, and with `P 𝒢`.

Then `P` holds on every coherent `𝒪_X`-module.

Nonemptiness cannot be dropped: on the empty Noetherian scheme hypotheses (1) and (2) hold for
`P := fun _ => False`, while the zero module is coherent. -/
@[stacks 01YI]
public theorem property_of_isCoherent_of_generic_stalk_of_nonempty
    (X : Scheme.{u}) [IsNoetherian X] (hX : Nonempty X) (P : X.Modules → Prop)
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hgeneric : ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ ξ : X, IsGenericPoint ξ (Set.range i.base) →
      ∃ G : X.Modules, _root_.SheafOfModules.IsCoherent G ∧
        SheafOfModules.supp G = Set.range i.base ∧
        Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
        (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val ξ
         Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
        P G) :
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → P F := by
  obtain ⟨x⟩ := hX
  obtain ⟨W, i, hci, hint, _⟩ :=
    IrreducibleDevissage.exists_isIntegral_isClosedImmersion_range_eq
      (⟨closure ({x} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
      isIrreducible_singleton.closure
  have : IsClosedImmersion i := hci
  have : IsIntegral W := hint
  obtain ⟨G, hGc, -, -, -, hGP⟩ :=
    hgeneric W i hci hint (i (genericPoint W)) (isGenericPoint_genericPoint_range i)
  exact property_of_isCoherent_of_generic_stalk X P
    (IrreducibleSupportDevissage.property_terminal_of_property X P hexact hGc hGP)
    hexact hgeneric

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
