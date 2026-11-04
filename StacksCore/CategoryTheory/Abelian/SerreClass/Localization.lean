module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import StacksCore.Algebra.Homology.ShortComplex.ShortExact

/-! # Serre quotients: faithful induced functors and short exact sequences

## When the induced functor on a Serre quotient is faithful

Stacks tag 06XK (Lemma 12.10.7). Let `A`, `B` be abelian categories, `F : A ⥤ B` exact, and let
`C ⊂ A` be a Serre subcategory contained in `Ker F`. Then `C = Ker F` if and only if the induced
functor `F̄ : A/C ⥤ B` is faithful.

The surrounding tags are all upstream. The quotient `A/C` together with its abelian structure is
tag 02MS, which Mathlib carries as `ObjectProperty.SerreClassLocalization.abelian`; `Ker F` is tag
02MR, `CategoryTheory.Functor.kernel`; and that `Ker F` is a Serre subcategory is 02MQ. What makes
`[P.IsSerreClass]` here mean *the Stacks project's* notion of a Serre subcategory, rather than a
Mathlib class that merely shares the name, is `isSerreClass_iff_prop_X₂_of_exact` in
`StacksCore.CategoryTheory.Abelian.SerreClass.Basic` (tag 02MP).

Both directions are stated for an arbitrary lift `G` of `F` through `L`, since lifts are unique up
to isomorphism; `faithful_liftOfLeKernel_iff` then specialises to the canonical one, which is the
`F̄` of the Stacks statement.

## Short exact sequences in the quotient

Let `L : A ⥤ A/C` be the localization functor. Since `L` is exact, it sends short exact sequences
to short exact sequences (`shortExact_map`), and every short exact sequence of `A/C` is isomorphic
to the image under `L` of a short exact sequence of `A` (`exists_shortExact_map_iso`): this is the
lifting of short exact sequences that the proof of Stacks 02MX (1) takes from the proofs of 02MS
and 05QG. `exact_map_iff` says that a short complex of `A` becomes exact in `A/C` if and only if
its homology lies in `C`; applied to the two short complexes of a 2-periodic complex
`(M, φ, ψ)`, this is the "in other words" of Stacks 02MX (2).

## Implementation notes

The prose above names the categories as the Stacks project does. In the code, the abelian
category `A` is called `C`, and the Serre subcategory `C` is the `ObjectProperty` `P`. As in
Mathlib's `ObjectProperty.SerreClassLocalization`, `A/C` is any category `D` with a localization
functor `L : C ⥤ D` for `P.isoModSerre`, a preadditive structure and `[L.Additive]`. The abelian
structure of `D` (tag 02MS) is not an assumption: a proof that needs it takes the local instance
`SerreClassLocalization.abelian L P`.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

open Limits

section Faithful

variable {C D B : Type*} [Category* C] [Category* D] [Category* B] [Abelian C] [Abelian B]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre]
  [Preadditive D] [L.Additive] {F : C ⥤ B}
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : D ⥤ B) (e : L ⋙ G ≅ F)

/-- An exact functor killing `f` kills the image of `f`: the image injects into the target after
applying `F`, and that mono is zero because it is preceded by the epi `F.map (factorThruImage f)`
onto it. -/
lemma isZero_obj_image_of_map_eq_zero {X Y : C} (f : X ⟶ Y) (hf : F.map f = 0) :
    IsZero (F.obj (Abelian.image f)) := by
  have : Mono (F.map (Abelian.image.ι f)) := F.map_mono _
  refine IsZero.of_mono_eq_zero (F.map (Abelian.image.ι f)) ?_
  rw [← cancel_epi (F.map (Abelian.factorThruImage f)), comp_zero, ← F.map_comp,
    Abelian.image.fac, hf]

omit [PreservesFiniteColimits F] in
include L P e in
/-- A lift of an exact functor through the localization is additive. -/
lemma additive_of_iso : G.Additive := by
  have : F.Additive := F.additive_of_preserves_binary_products
  have : (L ⋙ G).Additive := Functor.additive_of_iso e.symm
  exact (Localization.functor_additive_iff L P.isoModSerre G).2 inferInstance

include L P e in
/-- **Stacks 06XK**, for an arbitrary lift `G` of `F` through `L`.

Left to right: if `F X = 0` then `G` kills the identity of `L.obj X`, so faithfulness forces
`𝟙 (L.obj X) = 0`, i.e. `L.obj X` is a zero object, i.e. `X` lies in `P` by `isZero_obj_iff`.

Right to left: `P.isoModSerre` has a calculus of left fractions, so by
`Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions` it suffices to see that `G`
kills no nonzero morphism in the image of `L`. If `G (L f) = 0` then `F f = 0`, so the image of `f`
lies in `Ker F = P`, and `map_eq_zero_iff` gives `L f = 0`. -/
theorem faithful_iff : G.Faithful ↔ P = F.kernel := by
  have hG : G.Additive := additive_of_iso L P G e
  have hinv : P.isoModSerre.IsInvertedBy F := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _ e]
    exact MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts L _) _
  have hle : P ≤ F.kernel := P.le_kernel_of_isoModSerre_isInvertedBy F hinv
  constructor
  · intro _
    refine le_antisymm hle (fun X hX ↦ ?_)
    rw [← isZero_obj_iff L P, IsZero.iff_id_eq_zero]
    refine (G.map_injective_iff _ _).1 ?_
    rw [G.map_id, G.map_zero]
    exact ((e.app X).isZero_iff.2 ((prop_inverseImage_iff _ _ _).1 hX)).eq_of_src _ _
  · intro hP
    refine Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions L P.isoModSerre G
      (fun X Y f hf ↦ ?_)
    have hFf : F.map f = 0 := by
      have h := e.inv.naturality f
      rw [Functor.comp_map, hf, comp_zero] at h
      rw [← cancel_mono (e.inv.app Y), h, zero_comp]
    rw [map_eq_zero_iff L P]
    exact hP.ge _ ((prop_inverseImage_iff _ _ _).2 (isZero_obj_image_of_map_eq_zero f hFf))

section CanonicalLift

variable (F)

/-- The functor `F̄ : A/C ⥤ B` induced by an exact `F` whose kernel contains `C`. Exactness of `F`
turns `P ≤ F.kernel` into `P.isoModSerre.IsInvertedBy F`, which is what `Localization.lift`
wants. -/
noncomputable def liftOfLeKernel (hP : P ≤ F.kernel) : D ⥤ B :=
  Localization.lift F ((P.isoModSerre_isInvertedBy_iff F).2 hP) L

/-- The induced functor does lift `F`, that is `L ⋙ F̄ ≅ F`. -/
noncomputable def liftOfLeKernelFac (hP : P ≤ F.kernel) : L ⋙ liftOfLeKernel L P F hP ≅ F :=
  Localization.fac F _ L

/-- **Stacks 06XK.** For an exact `F : A ⥤ B` and a Serre subcategory `C ⊂ A` contained in `Ker F`,
the induced functor `F̄ : A/C ⥤ B` is faithful exactly when `C` is all of `Ker F`. -/
@[stacks 06XK]
theorem faithful_liftOfLeKernel_iff (hP : P ≤ F.kernel) :
    (liftOfLeKernel L P F hP).Faithful ↔ P = F.kernel :=
  faithful_iff L P _ (liftOfLeKernelFac L P F hP)

end CanonicalLift

end Faithful

section ShortExact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre]
  [Preadditive D] [L.Additive]

include P in
/-- The localization functor `L` sends short exact sequences to short exact sequences, since it
is exact (`preservesFiniteLimits` and `preservesFiniteColimits`, part of Stacks 02MS). The short
complex `S` is strict-implicit, so that `shortExact_map L P` is itself a proof of
`∀ ⦃S⦄, S.ShortExact → (S.map L).ShortExact`. -/
lemma shortExact_map ⦃S : ShortComplex C⦄ (hS : S.ShortExact) : (S.map L).ShortExact := by
  have := preservesFiniteLimits L P
  have := preservesFiniteColimits L P
  exact hS.map_of_exact L

include P in
/-- Every short exact sequence `S` of `D` is isomorphic to `T.map L` for some short exact
sequence `T` of `C`: the lifting of short exact sequences in the proof of Stacks 02MX (1), which
Stacks takes from the proofs of 02MS and 05QG.

By `epi_iff`, the arrow `S.g` is isomorphic to `L.map g` for an epimorphism `g` of `C`. The
kernel of `g` followed by `g` is short exact, and so is its image under `L`, which is then
isomorphic to `S` because a short exact sequence is determined up to isomorphism by its second
arrow (`ShortComplex.ShortExact.isoMk`). -/
lemma exists_shortExact_map_iso (S : ShortComplex D) (hS : S.ShortExact) :
    ∃ T : ShortComplex C, T.ShortExact ∧ Nonempty (T.map L ≅ S) := by
  let := abelian L P
  obtain ⟨X, Y, g, _, ⟨e⟩⟩ := (epi_iff L P S.g).1 hS.epi_g
  have hT := ShortComplex.shortExact_mk_kernel_ι g
  exact ⟨_, hT, ⟨(shortExact_map L P hT).isoMk hS ⟨e.hom.left, e.inv.left, by simp, by simp⟩
    ⟨e.hom.right, e.inv.right, by simp, by simp⟩ (Arrow.w_mk e.hom)⟩⟩

/-- **Stacks 02MX (2)**, exactness in the quotient: a short complex `T` becomes exact after
applying `L` if and only if its homology satisfies `P`.

For a 2-periodic complex `(M, φ, ψ)` (Stacks 02MW), that is `φ ψ : M ⟶ M` with `φ ≫ ψ = 0` and
`ψ ≫ φ = 0`, the homology objects of `ShortComplex.mk φ ψ _` and `ShortComplex.mk ψ φ _` are
`H⁰(M, φ, ψ) = Ker ψ / Im φ` and `H¹(M, φ, ψ) = Ker φ / Im ψ`. Applied to these two short
complexes, this lemma is the "in other words" of 02MX (2): `(M, φ, ψ)` becomes exact in the
quotient if and only if `H⁰(M, φ, ψ)` and `H¹(M, φ, ψ)` satisfy `P`. -/
@[stacks 02MX "(2): `(M, φ, ψ)` becomes exact in `D` iff its homology satisfies `P`"]
lemma exact_map_iff (T : ShortComplex C) : (T.map L).Exact ↔ P T.homology := by
  have := preservesFiniteLimits L P
  have := preservesFiniteColimits L P
  rw [ShortComplex.exact_iff_isZero_homology, (T.mapHomologyIso L).isZero_iff,
    isZero_obj_iff L P]

end ShortExact

end SerreClassLocalization

end CategoryTheory.ObjectProperty
