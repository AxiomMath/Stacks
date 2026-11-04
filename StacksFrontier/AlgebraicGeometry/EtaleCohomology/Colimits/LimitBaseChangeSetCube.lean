module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleSetsVerticalPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleSetSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange

/-!
# The cube of square comparisons of direct images, and the base change map of sheaves of sets

A commutative cube of schemes has a top square `(e₁, g₁, h₁, f₁)` and a bottom square
`(e₀, g₀, h₀, f₀)`, joined by four vertical morphisms `y, t, x, s`. Each of its six faces carries
the identification `Stacks.EtaleCohomology.LimitDirectImage.squarePushforwardIso` of its two
composite direct images, and these satisfy one coherence
(`Stacks.EtaleCohomology.LimitSetBaseChangeCube.squarePushforwardIso_cube_app`): going around the
cube from `g₀_* t_* e₁_*` to `s_* f₁_* h₁_*` through the bottom square and through the top square
gives the same identification. Its only input is the associativity pentagon
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc_app`, used six times.

The base change map `f^{-1}g_* ⟶ h_*e^{-1}` of sheaves of sets of a commutative square,
`Stacks.EtaleCohomology.smallEtaleSetBaseChange`, is the inverse mate of that square's
identification; transposed across the adjunction along `f` it is the direct image of the unit
followed by the identification
(`Stacks.EtaleCohomology.LimitSetBaseChangeCube.homEquiv_smallEtaleSetBaseChange_app`). This is
the form in which [Stacks, Tag 0EZT] (1) is proved.

## Main results

* `Stacks.EtaleCohomology.LimitSetBaseChangeCube.squarePushforwardIso_cube_app` — the cube.
* `Stacks.EtaleCohomology.LimitSetBaseChangeCube.homEquiv_smallEtaleSetBaseChange_app` — the
  transposed base change map.
* `Stacks.EtaleCohomology.LimitSetBaseChangeCube.bijective_homEquiv_comp_map_of_isIso` — for an
  invertible base change map, composing with its transpose is a bijection of hom-sets.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.LimitDirectImage

universe w' w u

namespace Stacks.EtaleCohomology.LimitSetBaseChangeCube

/-- The cancellation behind `squarePushforwardIso_cube_app`, in an arbitrary category: six
pentagons `π₁, …, π₆` and six inverse pairs. -/
theorem cube_algebra {𝒜 : Type*} [Category* 𝒜]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ OD : 𝒜}
    {m₁ : O₀ ⟶ O₁} {m₂ : O₁ ⟶ O₂} {n₂ : O₂ ⟶ O₁} {m₃ : O₂ ⟶ O₃} {m₄ : O₃ ⟶ O₄}
    {n₄ : O₄ ⟶ O₃} {m₅ : O₄ ⟶ O₅} {m₆ : O₅ ⟶ O₆} {n₆ : O₆ ⟶ O₅} {m₇ : O₆ ⟶ O₇}
    {m₈ : O₇ ⟶ O₈} {n₈ : O₈ ⟶ O₇} {r₁ : O₀ ⟶ O₉} {r₂ : O₉ ⟶ O₁₀} {q₂ : O₁₀ ⟶ O₉}
    {r₃ : O₁₀ ⟶ O₁₁} {r₄ : O₁₁ ⟶ O₈} {q₄ : O₈ ⟶ O₁₁}
    {k₁ : O₁ ⟶ OD} {k₃ : O₃ ⟶ OD} {k₅ : O₅ ⟶ OD} {k₇ : O₇ ⟶ OD} {k₉ : O₉ ⟶ OD}
    {k₁₁ : O₁₁ ⟶ OD}
    (e₂ : m₂ ≫ n₂ = 𝟙 _) (e₄ : m₄ ≫ n₄ = 𝟙 _) (e₆ : m₆ ≫ n₆ = 𝟙 _) (e₈ : m₈ ≫ n₈ = 𝟙 _)
    (e₁₀ : r₂ ≫ q₂ = 𝟙 _) (e₁₂ : r₄ ≫ q₄ = 𝟙 _)
    (π₁ : n₂ ≫ k₁ = m₃ ≫ k₃) (π₂ : m₅ ≫ k₅ = n₄ ≫ k₃) (π₃ : n₆ ≫ k₅ = m₇ ≫ k₇)
    (π₄ : q₄ ≫ k₁₁ = n₈ ≫ k₇) (π₅ : m₁ ≫ k₁ = r₁ ≫ k₉) (π₆ : r₃ ≫ k₁₁ = q₂ ≫ k₉) :
    ((m₁ ≫ m₂) ≫ (m₃ ≫ m₄) ≫ (m₅ ≫ m₆) ≫ (m₇ ≫ m₈)) ≫ q₄ ≫ k₁₁ =
      ((r₁ ≫ r₂) ≫ (r₃ ≫ r₄)) ≫ q₄ ≫ k₁₁ := by
  have l₈ : m₈ ≫ q₄ ≫ k₁₁ = k₇ := by rw [π₄, ← Category.assoc, e₈, Category.id_comp]
  have l₆ : m₆ ≫ m₇ ≫ k₇ = k₅ := by rw [← π₃, ← Category.assoc, e₆, Category.id_comp]
  have l₄ : m₄ ≫ m₅ ≫ k₅ = k₃ := by rw [π₂, ← Category.assoc, e₄, Category.id_comp]
  have l₂ : m₂ ≫ m₃ ≫ k₃ = k₁ := by rw [← π₁, ← Category.assoc, e₂, Category.id_comp]
  have r₄' : r₄ ≫ q₄ ≫ k₁₁ = k₁₁ := by rw [← Category.assoc, e₁₂, Category.id_comp]
  have r₂' : r₂ ≫ r₃ ≫ k₁₁ = k₉ := by rw [π₆, ← Category.assoc, e₁₀, Category.id_comp]
  simp only [Category.assoc]
  rw [l₈, l₆, l₄, l₂, π₅, r₄', r₂']

section Cube

variable {Y₁ T₁ X₁ S₁ Y₀ T₀ X₀ S₀ : Scheme.{u}}
  (e₁ : Y₁ ⟶ T₁) (g₁ : T₁ ⟶ S₁) (h₁ : Y₁ ⟶ X₁) (f₁ : X₁ ⟶ S₁)
  (e₀ : Y₀ ⟶ T₀) (g₀ : T₀ ⟶ S₀) (h₀ : Y₀ ⟶ X₀) (f₀ : X₀ ⟶ S₀)
  (y : Y₁ ⟶ Y₀) (t : T₁ ⟶ T₀) (x : X₁ ⟶ X₀) (s : S₁ ⟶ S₀)
  (d₁ : Y₁ ⟶ S₁) (hd₁e : d₁ = e₁ ≫ g₁) (hd₁h : d₁ = h₁ ≫ f₁)
  (d₀ : Y₀ ⟶ S₀) (hd₀e : d₀ = e₀ ≫ g₀) (hd₀h : d₀ = h₀ ≫ f₀)
  (a : Y₁ ⟶ T₀) (ha₁ : a = e₁ ≫ t) (ha₀ : a = y ≫ e₀)
  (b : T₁ ⟶ S₀) (hb₁ : b = g₁ ≫ s) (hb₀ : b = t ≫ g₀)
  (c : Y₁ ⟶ X₀) (hc₁ : c = h₁ ≫ x) (hc₀ : c = y ≫ h₀)
  (d : X₁ ⟶ S₀) (hd₁ : d = f₁ ≫ s) (hd₀ : d = x ≫ f₀)
  (D : Y₁ ⟶ S₀) (hDa : D = a ≫ g₀) (hDe : D = e₁ ≫ b) (hDy : D = y ≫ d₀) (hDc : D = c ≫ f₀)
  (hDh : D = h₁ ≫ d) (hDs : D = d₁ ≫ s)
  (A : Type w) [Category.{w'} A]

include hDa hDe hDy hDc hDh hDs in
/-- **The cube of square comparisons of direct images.** For a commutative cube of schemes with
top square `(e₁, g₁, h₁, f₁)`, bottom square `(e₀, g₀, h₀, f₀)` and vertical morphisms
`y, t, x, s`, the identification `g₀_* t_* e₁_* ≅ s_* f₁_* h₁_*` obtained through the `e`-face,
the bottom square, the `h`-face and the `f`-face is the one obtained through the `g`-face and the
top square. All six faces carry `Stacks.EtaleCohomology.LimitDirectImage.squarePushforwardIso`,
with their diagonals named. -/
theorem squarePushforwardIso_cube_app (N : Sheaf (smallEtaleTopology Y₁) A) :
    (smallEtalePushforward g₀ A).map
        ((squarePushforwardIso e₁ e₀ t y a ha₁ ha₀ A).inv.app N) ≫
      (squarePushforwardIso h₀ g₀ f₀ e₀ d₀ hd₀h hd₀e A).hom.app
          ((smallEtalePushforward y A).obj N) ≫
        (smallEtalePushforward f₀ A).map
            ((squarePushforwardIso h₁ h₀ x y c hc₁ hc₀ A).hom.app N) ≫
          (squarePushforwardIso f₁ f₀ s x d hd₁ hd₀ A).hom.app
            ((smallEtalePushforward h₁ A).obj N) =
    (squarePushforwardIso g₁ g₀ s t b hb₁ hb₀ A).hom.app ((smallEtalePushforward e₁ A).obj N) ≫
      (smallEtalePushforward s A).map
        ((squarePushforwardIso h₁ g₁ f₁ e₁ d₁ hd₁h hd₁e A).hom.app N) := by
  have π₁ := smallEtalePushforwardComp'_assoc_app y e₀ g₀ a ha₀ d₀ hd₀e D hDa hDy A N
  have π₂ := smallEtalePushforwardComp'_assoc_app y h₀ f₀ c hc₀ d₀ hd₀h D hDc hDy A N
  have π₃ := smallEtalePushforwardComp'_assoc_app h₁ x f₀ c hc₁ d hd₀ D hDc hDh A N
  have π₄ := smallEtalePushforwardComp'_assoc_app h₁ f₁ s d₁ hd₁h d hd₁ D hDs hDh A N
  have π₅ := smallEtalePushforwardComp'_assoc_app e₁ t g₀ a ha₁ b hb₀ D hDa hDe A N
  have π₆ := smallEtalePushforwardComp'_assoc_app e₁ g₁ s d₁ hd₁e b hb₁ D hDs hDe A N
  rw [← cancel_mono ((smallEtalePushforward s A).map
      ((smallEtalePushforwardComp' h₁ f₁ d₁ hd₁h A).hom.app N) ≫
    (smallEtalePushforwardComp' d₁ s D hDs A).hom.app N)]
  simp only [squarePushforwardIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp]
  exact cube_algebra
    (by simp [← Functor.map_comp])
    (Iso.inv_hom_id_app _ _)
    (by simp [← Functor.map_comp])
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)
    (by simp [← Functor.map_comp])
    π₁ π₂ π₃ π₄ π₅ π₆

end Cube

/-! ### The transposed base change map -/

section BaseChange

variable {X Y S T : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
  (w : e ≫ g = h ≫ f) (dd : Y ⟶ S) (hde : dd = e ≫ g) (hdh : dd = h ≫ f)

/-- **The base change map of sheaves of sets, transposed.** Transposed across the adjunction
`f^{-1} ⊣ f_*`, the base change map `f^{-1}g_*M ⟶ h_*e^{-1}M` of
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` is `g_*` of the unit `M ⟶ e_*e^{-1}M` followed by
the identification `g_*e_* ≅ f_*h_*` of the square,
`Stacks.EtaleCohomology.LimitDirectImage.squarePushforwardIso`. -/
theorem homEquiv_smallEtaleSetBaseChange_app
    (M : Sheaf (smallEtaleTopology T) (Type (u + 1))) :
    (smallEtaleInverseImageAdjunction.{u, 0} f).homEquiv _ _
        ((smallEtaleSetBaseChange.{u, 0} e h g f w).app M) =
      (smallEtalePushforward g (Type (u + 1))).map
          ((smallEtaleInverseImageAdjunction.{u, 0} e).unit.app M) ≫
        (squarePushforwardIso h g f e dd hdh hde (Type (u + 1))).hom.app
          ((smallEtaleInverseImage.{u, 0} e).obj M) := by
  have hβ : smallEtaleSetBaseChange.{u, 0} e h g f w =
      (mateEquiv (smallEtaleInverseImageAdjunction.{u, 0} e)
        (smallEtaleInverseImageAdjunction.{u, 0} f)).symm
        (TwoSquare.mk _ _ _ _ (smallEtaleSquarePushforwardIsoAt e h g f w (Type (u + 1))).hom) :=
    rfl
  have h₁ := unit_mateEquiv_symm (smallEtaleInverseImageAdjunction.{u, 0} e)
    (smallEtaleInverseImageAdjunction.{u, 0} f)
    (TwoSquare.mk _ _ _ _ (smallEtaleSquarePushforwardIsoAt e h g f w (Type (u + 1))).hom) M
  rw [Adjunction.homEquiv_unit, hβ]
  rw [smallEtaleSquarePushforwardIsoAt_eq_comp' e h g f w dd hde hdh] at h₁ ⊢
  exact h₁.symm

end BaseChange

/-- **An invertible map out of an inverse image, transposed, induces a bijection of hom-sets.** For
an adjunction `L ⊣ R` and an isomorphism `β : L(P) ⟶ Q`, composing the transpose of `β` with the
image under `R` is a bijection `(Q ⟶ M) ≃ (P ⟶ R(M))`. -/
theorem bijective_homEquiv_comp_map_of_isIso {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {P : C} {Q : D} (β : L.obj P ⟶ Q) [IsIso β]
    (M : D) : Function.Bijective (fun τ : Q ⟶ M => adj.homEquiv _ _ β ≫ R.map τ) := by
  have e : (fun τ : Q ⟶ M => adj.homEquiv _ _ β ≫ R.map τ) =
      (adj.homEquiv P M) ∘ (fun τ : Q ⟶ M => β ≫ τ) :=
    funext fun τ => (Adjunction.homEquiv_naturality_right _ _ _).symm
  rw [e]
  exact (Equiv.bijective _).comp
    ⟨fun _ _ hab => (cancel_epi β).mp hab, fun τ => ⟨inv β ≫ τ, by simp⟩⟩

end Stacks.EtaleCohomology.LimitSetBaseChangeCube

end
