module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
import StacksCore.Tactic.EgaSgaAttribute

/-! # Covering sieves are those whose sheafified inclusion is an isomorphism

For a category `C` with a topology `J`, an object `U` and a sieve `S` on `U`, Stacks 00ZO
characterises covering sieves: `S ∈ J U` if and only if the sheafification of the inclusion
`S ↪ h_U` is an isomorphism.

The Mathlib counterparts of the ingredients are `CategoryTheory.Sieve` for a sieve, with
`Sieve.functorInclusion` for the inclusion `S ↪ h_U`; `CategoryTheory.GrothendieckTopology` for a
topology, with `S ∈ J U` meaning `S` is covering; and `CategoryTheory.presheafToSheaf` for the
associated-sheaf functor `(-)^#`. Since `S^#` and `h_U^#` are sheaves, "isomorphism of presheaves"
is the same as `IsIso` in the sheaf category, which is how the statement is phrased. The category
`C` is taken to be small so that `Type`-valued sheafification is available unconditionally.

## Main results

* `sieve_sheafification_iff`: a sieve is covering if and only if the sheafification of its
  inclusion into the representable presheaf is an isomorphism (Stacks 00ZO).

Tags covered: 00ZO.
-/

@[expose] public section

open CategoryTheory

universe u

/-- **Stacks 00ZO.** A sieve `S` on `U` is a covering sieve for the topology `J` if and only if
the sheafification `S^# ⟶ h_U^#` of its inclusion `S ↪ h_U` (i.e. the image under the
associated-sheaf functor of `S.functorInclusion`) is an isomorphism. -/
@[stacks 00ZO,
  sga "4 II 5.3" "sieve inclusion S→h_U",
  sga "3 IV 4.3.12" "special case",
  sga "4 II 4.6.1" "more general",
  sga "4 II 5.1" "special case",
  sga "4 II 5.5" "Ψ ∘ Φ = id"]
theorem sieve_sheafification_iff {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (U : C) (S : Sieve U) :
    S ∈ J U ↔ IsIso ((presheafToSheaf J (Type u)).map S.functorInclusion) := by
  -- `presheafToSheaf` inverts exactly the local isomorphisms `J.W`,
  -- which (for `Type`-valued presheaves) are the locally bijective maps.
  rw [← GrothendieckTopology.W_iff, GrothendieckTopology.W_iff_isLocallyBijective]
  -- The sieve inclusion is always (locally) injective, being a monomorphism.
  have hinj : Presheaf.IsLocallyInjective J S.functorInclusion :=
    Presheaf.isLocallyInjective_of_injective J _ fun X =>
      ConcreteCategory.injective_of_mono_of_preservesPullback (S.functorInclusion.app X)
  -- For the sieve inclusion, the image sieve of an element `s : V ⟶ U`
  -- of `h_U` is exactly the pullback sieve `S.pullback s`.
  have himage : ∀ {V : C} (s : V ⟶ U),
      Presheaf.imageSieve S.functorInclusion s = S.pullback s := by
    intro V s
    ext W i
    constructor
    · rintro ⟨t, ht⟩
      rw [Sieve.pullback_apply, ← show t.val = i ≫ s from ht]
      exact t.2
    · exact fun hi => ⟨⟨i ≫ s, hi⟩, rfl⟩
  constructor
  · intro hS
    refine ⟨hinj, ⟨fun {V} s => ?_⟩⟩
    rw [himage s]
    exact J.pullback_stable s hS
  · rintro ⟨_, hsurj⟩
    simpa [himage (𝟙 U)] using hsurj.imageSieve_mem (U := U) (𝟙 U)
