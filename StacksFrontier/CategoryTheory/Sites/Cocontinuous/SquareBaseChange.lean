module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Base change across a commuting square of site functors

Let `a : 𝒳' ⥤ 𝒴'`, `b : 𝒳' ⥤ 𝒳`, `c : 𝒳 ⥤ 𝒴` and `d : 𝒴' ⥤ 𝒴` be continuous functors of sites
with `a ⋙ d = b ⋙ c`, let `a` and `c` moreover be cocontinuous, and let the restrictions along
`b` and along `d` admit left adjoints `g'_!` and `g_!`. The square carries two base-change
comparisons, one between the direct images,

`c_* ∘ d^{-1} ⟶ b^{-1} ∘ a_*`,

and one between the lower shrieks,

`a^{-1} ∘ g'_! ⟶ g_! ∘ c^{-1}`.

Both are mates of the single 2-cell saying that restriction along `d` followed by restriction
along `a` is restriction along `c` followed by restriction along `b`, and one is invertible
exactly when the other is.

## Main definitions

* `CategoryTheory.Sites.inverseImageTwoSquare`: the 2-cell of the square, an isomorphism.
* `CategoryTheory.Sites.pushforwardBaseChange` and
  `CategoryTheory.Sites.lowerShriekBaseChange`: the two canonical comparisons.

## Main results

* `CategoryTheory.isIso_mateEquiv_iff_isIso_mateEquiv_symm`: in a square of four left adjoints,
  a 2-cell has invertible mate along the vertical adjunctions if and only if its mate along the
  horizontal ones is invertible.
* `CategoryTheory.Sites.isIso_pushforwardBaseChange_iff`: the two base-change comparisons of a
  commuting square of site functors are invertible together.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Adjunction

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Adjunctions

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)

/-- **In a square of four left adjoints the two mates of a 2-cell are invertible together.** For
`α : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂`, the mate `U₂ ⋙ R₁ ⟶ R₂ ⋙ U₁` taken along `adj₃` and `adj₄` is an
isomorphism if and only if the mate `F₁ ⋙ L₂ ⟶ L₁ ⋙ F₂` taken along `adj₁` and `adj₂` is. -/
theorem isIso_mateEquiv_iff_isIso_mateEquiv_symm (α : TwoSquare R₁ F₂ F₁ R₂) :
    IsIso (mateEquiv adj₄ adj₃ α).natTrans ↔
      IsIso ((mateEquiv adj₁ adj₂).symm α).natTrans := by
  have key : (mateEquiv adj₄ adj₃ α).natTrans =
      conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)
        ((mateEquiv adj₁ adj₂).symm α).natTrans := by
    conv_lhs => rw [← (mateEquiv adj₁ adj₂).apply_symm_apply α]
    exact iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ _
  rw [key]
  exact ⟨fun _ => conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) _,
    fun _ => inferInstance⟩

end Adjunctions

namespace Sites

universe w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄ wA tA

variable {X' : Type w₁} {Y' : Type w₂} {X : Type w₃} {Y : Type w₄}
  [Category.{t₁} X'] [Category.{t₂} Y'] [Category.{t₃} X] [Category.{t₄} Y]
  (J' : GrothendieckTopology X') (K' : GrothendieckTopology Y')
  (J : GrothendieckTopology X) (K : GrothendieckTopology Y)
  (a : X' ⥤ Y') (b : X' ⥤ X) (c : X ⥤ Y) (d : Y' ⥤ Y)
  (A : Type wA) [Category.{tA} A]
  [a.IsContinuous J' K'] [b.IsContinuous J' J] [c.IsContinuous J K] [d.IsContinuous K' K]
  (hsq : a ⋙ d = b ⋙ c)

/-- **The square of inverse images commutes.** Restriction along `d` followed by restriction
along `a` is restriction along `a ⋙ d = b ⋙ c`, hence restriction along `c` followed by
restriction along `b`. -/
def inverseImageSquareIso :
    d.sheafPushforwardContinuous A K' K ⋙ a.sheafPushforwardContinuous A J' K' ≅
      c.sheafPushforwardContinuous A J K ⋙ b.sheafPushforwardContinuous A J' J :=
  haveI := Functor.isContinuous_comp a d J' K' K
  haveI := Functor.isContinuous_comp b c J' J K
  Functor.sheafPushforwardContinuousIso (eqToIso hsq) A J' K

/-- The 2-cell of the commuting square, namely
`CategoryTheory.Sites.inverseImageSquareIso` read as a 2-square. -/
def inverseImageTwoSquare :
    TwoSquare (d.sheafPushforwardContinuous A K' K) (c.sheafPushforwardContinuous A J K)
      (a.sheafPushforwardContinuous A J' K') (b.sheafPushforwardContinuous A J' J) :=
  (inverseImageSquareIso J' K' J K a b c d A hsq).hom

/-- The 2-cell `CategoryTheory.Sites.inverseImageTwoSquare` is an isomorphism. -/
instance isIso_inverseImageTwoSquare :
    IsIso (inverseImageTwoSquare J' K' J K a b c d A hsq).natTrans :=
  inferInstanceAs (IsIso (inverseImageSquareIso J' K' J K a b c d A hsq).hom)

section

variable [a.IsCocontinuous J' K'] [c.IsCocontinuous J K]
  [∀ F : X'ᵒᵖ ⥤ A, a.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ A, c.op.HasPointwiseRightKanExtension F]

/-- **The base-change comparison of the direct images.** For a commuting square of site functors
whose two horizontal arrows `a` and `c` are continuous and cocontinuous, the mate of
`CategoryTheory.Sites.inverseImageTwoSquare` along the adjunctions `a^{-1} ⊣ a_*` and
`c^{-1} ⊣ c_*` is a natural transformation `c_* ∘ d^{-1} ⟶ b^{-1} ∘ a_*`. -/
def pushforwardBaseChange :
    c.sheafPushforwardCocontinuous A J K ⋙ d.sheafPushforwardContinuous A K' K ⟶
      b.sheafPushforwardContinuous A J' J ⋙ a.sheafPushforwardCocontinuous A J' K' :=
  (mateEquiv (c.sheafAdjunctionCocontinuous A J K) (a.sheafAdjunctionCocontinuous A J' K')
    (inverseImageTwoSquare J' K' J K a b c d A hsq)).natTrans

variable {shriekX : Sheaf J' A ⥤ Sheaf J A} {shriekY : Sheaf K' A ⥤ Sheaf K A}
  (adjX : shriekX ⊣ b.sheafPushforwardContinuous A J' J)
  (adjY : shriekY ⊣ d.sheafPushforwardContinuous A K' K)

/-- **The base-change comparison of the lower shrieks.** With the left adjoint `g'_!` of
restriction along `b` and the left adjoint `g_!` of restriction along `d` given, the mate of
`CategoryTheory.Sites.inverseImageTwoSquare` along those two adjunctions is a natural
transformation `a^{-1} ∘ g'_! ⟶ g_! ∘ c^{-1}`. -/
def lowerShriekBaseChange :
    a.sheafPushforwardContinuous A J' K' ⋙ shriekX ⟶
      shriekY ⋙ c.sheafPushforwardContinuous A J K :=
  ((mateEquiv adjY adjX).symm
    (inverseImageTwoSquare J' K' J K a b c d A hsq)).natTrans

/-- **The two base-change comparisons of a commuting square of site functors are invertible
together.** The comparison `c_* ∘ d^{-1} ⟶ b^{-1} ∘ a_*` of the direct images is an isomorphism
if and only if the comparison `a^{-1} ∘ g'_! ⟶ g_! ∘ c^{-1}` of the lower shrieks is. -/
theorem isIso_pushforwardBaseChange_iff :
    IsIso (pushforwardBaseChange J' K' J K a b c d A hsq) ↔
      IsIso (lowerShriekBaseChange J' K' J K a b c d A hsq adjX adjY) :=
  isIso_mateEquiv_iff_isIso_mateEquiv_symm adjY adjX
    (a.sheafAdjunctionCocontinuous A J' K') (c.sheafAdjunctionCocontinuous A J K) _

end

end Sites

end CategoryTheory

end
