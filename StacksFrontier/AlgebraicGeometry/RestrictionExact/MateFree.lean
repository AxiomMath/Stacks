module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Commuting left adjoints without a Beck--Chevalley condition

Given four adjunctions `Lᵢ ⊣ Rᵢ` arranged in a square, the mate of an isomorphism
`R₁ ⋙ R₂ ≅ R₃ ⋙ R₄` is a *map* between the composites of left adjoints and is in general not
invertible; that is the Beck--Chevalley condition. But if the square of **right** adjoints
commutes, the square of left adjoints commutes for free: both `L₂ ⋙ L₁` and `L₄ ⋙ L₃` are left
adjoint to one and the same functor, and a left adjoint is unique up to canonical isomorphism.

## Main results

* `Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm`:
  `R₁ ⋙ R₂ ≅ R₃ ⋙ R₄` gives `L₂ ⋙ L₁ ≅ L₄ ⋙ L₃`.

## Route

`Adjunction.comp` gives `L₂ ⋙ L₁ ⊣ R₁ ⋙ R₂`; `Adjunction.ofNatIsoRight` transports that along
the given isomorphism to `L₂ ⋙ L₁ ⊣ R₃ ⋙ R₄`, which `Adjunction.leftAdjointUniq` then compares
with `L₄ ⋙ L₃ ⊣ R₃ ⋙ R₄`.

## Implementation notes

The point of recording this is which square one has to verify. For the restriction comparison
that [Stacks, Tag 01SB] needs — that the quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules` commutes with restriction to an
open `V ⊆ S` — the square of direct images
`pushforward ⋙ restriction ≅ restriction ⋙ pushforward` is the *wrong* square: its mate is the
Beck--Chevalley map, and nothing makes that invertible. The square to verify instead is the one
built from the **right adjoints of the restrictions**, which by
`SheafOfModules.overPushforwardOverAdj` are again `SheafOfModules.pushforward`s, so that square
is an identification of pushforwards along two composite site functors.

## What is not done

**This file does not prove Lemma A of [Stacks, Tag 01SB]**, i.e. it does not construct the
restriction comparison for `pullbackModules`. It supplies only the
category-theoretic step that removes the Beck--Chevalley obstruction from the route. What the
comparison still needs, over an open `V ⊆ S` with `U = f ⁻¹ᵁ V`, is recorded here:

* the slice-site direct image `SheafOfModules (𝒪_X.over U) ⥤ SheafOfModules ((f_*𝒪_X).over V)`,
  which is `SheafOfModules.pushforward` along `CategoryTheory.Over.post (Opens.map f.base)`, and
  its left adjoint. Blocker: `(Over.post (Opens.map f.base)).IsContinuous (J.over V) (K.over U)`
  does **not** synthesize at this pin. Mathlib derives continuity of `Over.post F` from
  `Functor.PreservesOneHypercovers F`, and `PreservesOneHypercovers (Opens.map f.base)` does not
  synthesize either; the available alternative is
  `CategoryTheory.CoverPreserving.overPost` together with `CompatiblePreserving`.
* the identification of `SheafOfModules.pushforward (pushforwardOver U) ⋙ pushforward` with
  `pushforward ⋙ pushforward (pushforwardOver V)`, by `SheafOfModules.pushforwardComp` twice.
  The two composite site functors `Opens S ⥤ Over U` here are
  `Opens.map f.base ⋙ Over.star U` and `Over.star V ⋙ Over.post (Opens.map f.base)`. They are
  **equal but not definitionally so**: `W ⨯ V = W ⊓ V` in `Opens S` holds only up to
  `le_antisymm` of `Limits.prod.fst`/`prod.snd` against `Limits.prod.lift`, since
  `HasBinaryProducts (Opens S)` is not the lattice meet on the nose. What *is* definitional, and
  was checked, is that `Opens.map` commutes with `⊓` and with composition, and that
  `Over.post F ⋙ Over.forget _ = Over.forget _ ⋙ F`.

An alternative formulation avoiding slice sites altogether — take `V` and `U` as open
*subschemes*, so that restriction is `SheafOfModules.pushforward` along
`IsOpenMap.functor` with right adjoint the pushforward along `Opens.map`, and the two composite
site functors become `Opens.map` of the two equal composites `U ⟶ X ⟶ S` and `U ⟶ V ⟶ S` — was
not carried out, but it replaces every `Over.star`/`Over.post` step above by an `Opens.map`
step, and `Opens.map (a ≫ b) = Opens.map b ⋙ Opens.map a` holds by `rfl`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.CategoryTheory

variable {A : Type u₁} {B : Type u₂} {B' : Type u₃} {E : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} B'] [Category.{v₄} E]

/-- **If a square of right adjoints commutes, so does the square of left adjoints.**
No Beck--Chevalley condition is involved: `L₂ ⋙ L₁` and `L₄ ⋙ L₃` are both left adjoint to
`R₃ ⋙ R₄`, and a left adjoint is unique up to canonical isomorphism. -/
noncomputable def leftAdjointsCommOfRightAdjointsComm {L₁ : B ⥤ A} {R₁ : A ⥤ B} {L₂ : E ⥤ B}
    {R₂ : B ⥤ E} {L₃ : B' ⥤ A} {R₃ : A ⥤ B'} {L₄ : E ⥤ B'} {R₄ : B' ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) : L₂ ⋙ L₁ ≅ L₄ ⋙ L₃ :=
  Adjunction.leftAdjointUniq ((adj₂.comp adj₁).ofNatIsoRight e) (adj₄.comp adj₃)

end Stacks.CategoryTheory

end
