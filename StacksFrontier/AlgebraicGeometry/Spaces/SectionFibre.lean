module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# The fibre of a morphism of algebraic spaces over a section

Let `S` be a scheme contained in a big fppf site `B`, let `F₁` and `F₂` be algebraic spaces
over `S`, let `g : F₁ ⟶ F₂` and let `σ : 1 ⟶ F₂` be a section, where `1` is the presheaf of
points of the final object of the big fppf site of `S`. The fibre product `Z = F₁ ×_{F₂} 1`
is again an algebraic space over `S`. This is the case of Stacks 02X2 in which one of the two
factors is the final object.

## Main results

* `CategoryTheory.Limits.isPullback_diag_of_mono`: the diagonal of a subobject is the base
  change of the diagonal of the ambient object.
* `CategoryTheory.Limits.IsPullback.of_diag_prodLift_isTerminal`: a pullback of a diagonal
  `Y ⟶ Y ⨯ Y` along `prod.lift u (! ≫ t)`, for `t` a morphism out of a final object, is the
  fibre product of `u` and `t`.
* `AlgebraicGeometry.isAlgebraicSpace_of_isPullback_isTerminal`: the fibre of a morphism of
  algebraic spaces over a section is an algebraic space.
* `AlgebraicGeometry.isAlgebraicSpace_pullback_of_isTerminal`,
  `AlgebraicGeometry.isAlgebraicSpace_pullback_terminal` and
  `AlgebraicGeometry.isAlgebraicSpace_pullback_mkId`: the same statement for the chosen fibre
  product, the last two for the chosen final object `⊤` and for the final object `S / S` of
  the big fppf site of `S`.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- If `m : Z ⟶ Y` is a monomorphism, then the diagonal of `Z` is the base change of the
diagonal of `Y` along `m ⨯ m : Z ⨯ Z ⟶ Y ⨯ Y`. -/
lemma isPullback_diag_of_mono {Z Y : C} (m : Z ⟶ Y) [Mono m] :
    IsPullback m (diag Z) (diag Y) (prod.map m m) := by
  have key : ∀ s : PullbackCone (diag Y) (prod.map m m),
      s.fst = s.snd ≫ prod.fst ≫ m ∧ s.snd ≫ prod.fst = s.snd ≫ prod.snd := by
    intro s
    have h₁ : s.fst = s.snd ≫ prod.fst ≫ m := by simpa using s.condition =≫ prod.fst
    have h₂ : s.fst = s.snd ≫ prod.snd ≫ m := by simpa using s.condition =≫ prod.snd
    exact ⟨h₁, by rw [← cancel_mono m, Category.assoc, Category.assoc, ← h₁, ← h₂]⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun s => s.snd ≫ prod.fst) (fun s => by simp [(key s).1]) (fun s => ?_)
    (fun s l _ hl => by rw [← hl]; simp))
  refine prod.hom_ext ?_ ?_ <;> simp [(key s).2]

/-- Let `t : One ⟶ Y` be a morphism out of a final object and let `u : X ⟶ Y`. A pullback of
the diagonal `Y ⟶ Y ⨯ Y` along `prod.lift u (! ≫ t)` is a fibre product of `u` and `t`. -/
lemma IsPullback.of_diag_prodLift_isTerminal {Y X One P : C} (hOne : IsTerminal One)
    {t : One ⟶ Y} {u : X ⟶ Y} {k : P ⟶ Y} {l : P ⟶ X}
    (h : IsPullback k l (diag Y) (prod.lift u (hOne.from X ≫ t))) :
    IsPullback l (hOne.from P) u t := by
  have hk₁ : k = l ≫ u := by simpa using h.w =≫ prod.fst
  have hk₂ : k = l ≫ hOne.from X ≫ t := by simpa using h.w =≫ prod.snd
  have hw : l ≫ u = hOne.from P ≫ t := by
    rw [← hk₁, hk₂, ← Category.assoc, hOne.hom_ext (l ≫ hOne.from X) (hOne.from P)]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => h.lift (s.fst ≫ u) s.fst ?_) (fun s => by simp)
    (fun s => hOne.hom_ext _ _) (fun s l' hl₁ _ => ?_))
  · refine prod.hom_ext (by simp) ?_
    simp [s.condition, reassoc_of% hOne.hom_ext (s.fst ≫ hOne.from X) s.snd]
  · refine h.hom_ext ?_ (by simpa using hl₁)
    rw [h.lift_fst, hk₁, ← Category.assoc, hl₁]

end CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F₁ F₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `F₁` and `F₂` be algebraic spaces over `S`, let `g : F₁ ⟶ F₂`, let `T` be a final
object of the big fppf site of `S` and let `σ : yoneda.obj T ⟶ F₂` be a section of `F₂`. Then a
fibre product `Z` of `g` and `σ` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_of_isPullback_isTerminal
    (h₁ : IsAlgebraicSpace B S hS F₁) (h₂ : IsAlgebraicSpace B S hS F₂)
    {T : BigFppfOver B S hS} (hT : IsTerminal T) {g : F₁ ⟶ F₂} {σ : yoneda.obj T ⟶ F₂}
    {m : Z ⟶ F₁} {p : Z ⟶ yoneda.obj T} (hZ : IsPullback m p g σ) :
    IsAlgebraicSpace B S hS Z := by
  have hTerm : IsTerminal (yoneda.obj T) := hT.isTerminalObj yoneda T
  have hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z := by
    refine ObjectProperty.prop_of_isLimit _ hZ.isLimit ?_
    rintro (_ | _ | _)
    exacts [h₂.isSheaf, h₁.isSheaf, ObjectProperty.prop_of_isTerminal _ _ hTerm]
  have hmono : Mono m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms _) hZ.flip (hTerm.mono_from σ)
  obtain ⟨U, f, hsurj, hetale⟩ := h₁.exists_atlas
  obtain ⟨V, s₀, k₀, hpb⟩ :=
    h₂.diagonal_representable (prod.lift (f ≫ g) (hTerm.from (yoneda.obj U) ≫ σ))
  have hsmall := (IsPullback.of_diag_prodLift_isTerminal hTerm hpb).of_bot' hZ
  exact ⟨hsheaf, MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_diag_of_mono m) h₁.diagonal_representable, V, _,
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback
      hsmall hsurj,
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback
      hsmall hetale⟩

/-- The chosen fibre product of a morphism of algebraic spaces over `S` and a section over a final
object of the big fppf site of `S` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_pullback_of_isTerminal
    (h₁ : IsAlgebraicSpace B S hS F₁) (h₂ : IsAlgebraicSpace B S hS F₂)
    {T : BigFppfOver B S hS} (hT : IsTerminal T) (g : F₁ ⟶ F₂) (σ : yoneda.obj T ⟶ F₂) :
    IsAlgebraicSpace B S hS (pullback g σ) :=
  isAlgebraicSpace_of_isPullback_isTerminal h₁ h₂ hT (IsPullback.of_hasPullback g σ)

/-- The chosen fibre product of a morphism of algebraic spaces over `S` and a section over the
chosen final object of the big fppf site of `S` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_pullback_terminal
    (h₁ : IsAlgebraicSpace B S hS F₁) (h₂ : IsAlgebraicSpace B S hS F₂) (g : F₁ ⟶ F₂)
    (σ : yoneda.obj (⊤_ (BigFppfOver B S hS)) ⟶ F₂) :
    IsAlgebraicSpace B S hS (pullback g σ) :=
  isAlgebraicSpace_pullback_of_isTerminal h₁ h₂ terminalIsTerminal g σ

/-- The chosen fibre product of a morphism of algebraic spaces over `S` and a section over the
final object `S / S` of the big fppf site of `S` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_pullback_mkId
    (h₁ : IsAlgebraicSpace B S hS F₁) (h₂ : IsAlgebraicSpace B S hS F₂) (g : F₁ ⟶ F₂)
    (σ : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ⟶ F₂) :
    IsAlgebraicSpace B S hS (pullback g σ) :=
  isAlgebraicSpace_pullback_of_isTerminal h₁ h₂ Over.mkIdTerminal g σ

end AlgebraicGeometry

end
