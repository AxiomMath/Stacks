module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.CharacterTwist

/-!
# The character twist travels along a left adjoint of restriction

Let `H : C ⥤ D` be a continuous functor of sites, let a group `G` act by automorphisms on an
object `W` of `C` and let `χ : G → ℤˣ` be a character.  The twist `ℤ(χ)` of the free abelian
sheaf on `W` is then formed twice over: once on `(C, J)`, and once on `(D, K)` for the image
`H W` with the induced action.  If restriction along `H` has a left adjoint `L`, the two twists
are related by

`L ℤ(χ)_C ≅ ℤ(χ)_D`.

Both sides corepresent the same functor — the `χ`-semi-invariant sections over `W`, which
restriction along `H` does not change — so the comparison is the Yoneda-style one, with no
computation of `L`.

Two instances of this are what the alternating Čech development of [Stacks, Tag 0728] needs.
For `H = Over.forget Q` and `L` extension by zero it says that a twist on the ambient site is
extended by zero from the localization at `Q`, whenever the action is an action over `Q`; this
is the specialization `CategoryTheory.characterTwistSliceIso`.  For `H` an equivalence of sites
and `L` the inverse of restriction it says that the twist is carried to the twist by the induced
equivalence of sheaf categories.

## Main definitions

* `CategoryTheory.forgetAut` is the action of `G` on `W.left` underlying an action on an object
  `W` of a slice category.
* `CategoryTheory.characterTwistPushforwardHomEquiv` identifies the maps out of `L ℤ(χ)_C` with
  the `χ`-semi-invariant sections over `H W`.
* `CategoryTheory.characterTwistPushforwardComparison` is the comparison morphism
  `L ℤ(χ)_C ⟶ ℤ(χ)_D`, and `CategoryTheory.characterTwistPushforwardIso` the resulting
  isomorphism; `CategoryTheory.characterTwistSliceIso` is its extension-by-zero
  specialization.

## Main results

* `CategoryTheory.characterSections_sheafPushforwardContinuous`: restricting a sheaf along `H`
  does not change the `χ`-semi-invariant sections over `W` — they are the same subgroup of the
  same group.
* `CategoryTheory.characterTwistPushforwardComparison_comp`: the comparison morphism induces the
  identification of maps out of the two twists, which is what makes it an isomorphism.
* `CategoryTheory.isIso_characterTwistPushforwardComparison`: **the comparison morphism is an
  isomorphism.**

## Implementation notes

The left adjoint is not constructed here: it is taken as any left adjoint of
`CategoryTheory.Functor.sheafPushforwardContinuous`, which is how the consumers of this file
already have it — extension by zero needs a left Kan extension along `H.op` to exist pointwise,
and the inverse of an equivalence needs nothing.  Nothing below uses more about the adjunction
than its unit and counit.

That the two subgroups of `χ`-semi-invariant sections coincide is an equality and not an
isomorphism: the sections of the restriction of `F` over `W` are the sections of `F` over `H W`
by definition of the restriction, and the automorphism of `H W` realizing a group element is the
image of the automorphism of `W` realizing it.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
-/

@[expose] public noncomputable section

universe w v u₁ u₂

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    (H : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [H.IsContinuous J K] (W : C) {G : Type w} [Group G] (act : G →* Aut W) (χ : G →* ℤˣ)
    [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]

omit [HasSheafify J AddCommGrpCat] [HasSheafify K AddCommGrpCat] in
/-- **Restriction along `H` does not change the `χ`-semi-invariant sections over `W`.**  The
sections of the restriction of `F` over `W` are the sections of `F` over `H W`, and the
automorphism of `H W` realizing a group element is the image of the automorphism of `W`
realizing it. -/
theorem characterSections_sheafPushforwardContinuous (F : Sheaf K AddCommGrpCat.{v}) :
    characterSections W act χ
        ((H.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj F).obj =
      characterSections (H.obj W) ((Functor.mapAut W H).comp act) χ F.obj :=
  rfl

section Adjunction

variable {L : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf K AddCommGrpCat.{v}}
    (adj : L ⊣ H.sheafPushforwardContinuous AddCommGrpCat.{v} J K)

/-- **The maps out of `L ℤ(χ)_C` are the `χ`-semi-invariant sections over `H W`.**  By the
adjunction they are the maps out of `ℤ(χ)_C` into the restriction of `F`, which are the
`χ`-semi-invariant sections of that restriction over `W` — the same subgroup. -/
def characterTwistPushforwardHomEquiv (F : Sheaf K AddCommGrpCat.{v}) :
    (L.obj (characterTwist W act χ J) ⟶ F) ≃
      characterSections (H.obj W) ((Functor.mapAut W H).comp act) χ F.obj :=
  (adj.homEquiv _ _).trans (characterTwistHomEquiv W act χ J _)

omit [HasSheafify K AddCommGrpCat] in
/-- Naturality in the coefficients of the identification of maps out of `L ℤ(χ)_C` with the
`χ`-semi-invariant sections. -/
theorem characterTwistPushforwardHomEquiv_comp {F F' : Sheaf K AddCommGrpCat.{v}}
    (u : L.obj (characterTwist W act χ J) ⟶ F) (k : F ⟶ F') :
    ((characterTwistPushforwardHomEquiv H J K W act χ adj F' (u ≫ k)) :
        F'.obj.obj (op (H.obj W))) =
      (k.hom.app (op (H.obj W)))
        ((characterTwistPushforwardHomEquiv H J K W act χ adj F u) :
          F.obj.obj (op (H.obj W))) := by
  change ((characterTwistHomEquiv W act χ J _ ((adj.homEquiv _ _) (u ≫ k))).1) = _
  rw [adj.homEquiv_naturality_right]
  exact characterTwistHomEquiv_comp W act χ J ((adj.homEquiv _ _) u)
    ((H.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map k)

/-- The identification of the maps out of the two twists: both are the `χ`-semi-invariant
sections over `H W`. -/
def characterTwistPushforwardHomCompare (F : Sheaf K AddCommGrpCat.{v}) :
    (characterTwist (H.obj W) ((Functor.mapAut W H).comp act) χ K ⟶ F) ≃
      (L.obj (characterTwist W act χ J) ⟶ F) :=
  (characterTwistHomEquiv (H.obj W) ((Functor.mapAut W H).comp act) χ K F).trans
    (characterTwistPushforwardHomEquiv H J K W act χ adj F).symm

/-- **The comparison morphism `L ℤ(χ)_C ⟶ ℤ(χ)_D`**: the map out of `L ℤ(χ)_C` attached to the
`χ`-semi-invariant section of `ℤ(χ)_D` over `H W` which the identity of `ℤ(χ)_D` is. -/
def characterTwistPushforwardComparison :
    L.obj (characterTwist W act χ J) ⟶
      characterTwist (H.obj W) ((Functor.mapAut W H).comp act) χ K :=
  characterTwistPushforwardHomCompare H J K W act χ adj _ (𝟙 _)

/-- **The comparison morphism induces the identification of maps out of the two twists.**  Both
identifications are natural in the coefficients and take the same value on the identity. -/
theorem characterTwistPushforwardComparison_comp {F : Sheaf K AddCommGrpCat.{v}}
    (u : characterTwist (H.obj W) ((Functor.mapAut W H).comp act) χ K ⟶ F) :
    characterTwistPushforwardComparison H J K W act χ adj ≫ u =
      characterTwistPushforwardHomCompare H J K W act χ adj F u := by
  have key : (characterTwistPushforwardHomEquiv H J K W act χ adj F)
      (characterTwistPushforwardComparison H J K W act χ adj ≫ u) =
      characterTwistHomEquiv (H.obj W) ((Functor.mapAut W H).comp act) χ K F u := by
    refine Subtype.ext ?_
    rw [characterTwistPushforwardHomEquiv_comp]
    have h1 : (characterTwistPushforwardHomEquiv H J K W act χ adj
          (characterTwist (H.obj W) ((Functor.mapAut W H).comp act) χ K))
        (characterTwistPushforwardComparison H J K W act χ adj) =
        characterTwistHomEquiv (H.obj W) ((Functor.mapAut W H).comp act) χ K _ (𝟙 _) :=
      (characterTwistPushforwardHomEquiv H J K W act χ adj _).apply_symm_apply _
    rw [h1, ← characterTwistHomEquiv_comp (H.obj W) ((Functor.mapAut W H).comp act) χ K (𝟙 _) u,
      Category.id_comp]
  change _ = (characterTwistPushforwardHomEquiv H J K W act χ adj F).symm
    (characterTwistHomEquiv (H.obj W) ((Functor.mapAut W H).comp act) χ K F u)
  rw [← key, Equiv.symm_apply_apply]

/-- **The twist on `(D, K)` is the image of the twist on `(C, J)` under the left adjoint of
restriction.**  The comparison morphism is an isomorphism, because precomposition with it is the
bijection of `characterTwistPushforwardHomCompare` on maps into every coefficient sheaf. -/
theorem isIso_characterTwistPushforwardComparison :
    IsIso (characterTwistPushforwardComparison H J K W act χ adj) := by
  obtain ⟨u, hu⟩ := (characterTwistPushforwardHomCompare H J K W act χ adj
    (L.obj (characterTwist W act χ J))).surjective (𝟙 _)
  have h1 : characterTwistPushforwardComparison H J K W act χ adj ≫ u = 𝟙 _ := by
    rw [characterTwistPushforwardComparison_comp]
    exact hu
  refine ⟨u, h1, ?_⟩
  refine (characterTwistPushforwardHomCompare H J K W act χ adj
    (characterTwist (H.obj W) ((Functor.mapAut W H).comp act) χ K)).injective ?_
  simp only [← characterTwistPushforwardComparison_comp]
  rw [← Category.assoc, h1, Category.id_comp, Category.comp_id]

/-- **The twist on `(D, K)` is the image of the twist on `(C, J)` under the left adjoint of
restriction**, as an isomorphism. -/
def characterTwistPushforwardIso :
    L.obj (characterTwist W act χ J) ≅
      characterTwist (H.obj W) ((Functor.mapAut W H).comp act) χ K :=
  @asIso _ _ _ _ _ (isIso_characterTwistPushforwardComparison H J K W act χ adj)

end Adjunction

/-! ### The extension-by-zero specialization -/

section Slice

/-- The action of `G` on the underlying object of `W` induced by an action on `W` in the slice
category over `Q`. -/
abbrev forgetAut {Q : C} (W' : Over Q) (act' : G →* Aut W') : G →* Aut W'.left :=
  (Functor.mapAut W' (Over.forget Q)).comp act'

/-- **The extension by zero of the twist on the slice at `Q` is the twist on the ambient
site.**  This is `CategoryTheory.characterTwistPushforwardIso` at `H = Over.forget Q`. -/
def characterTwistSliceIso {Q : C} (W' : Over Q) (act' : G →* Aut W') (χ' : G →* ℤˣ)
    (J' : GrothendieckTopology C) [HasSheafify J' AddCommGrpCat.{v}]
    [HasSheafify (J'.over Q) AddCommGrpCat.{v}]
    {L : Sheaf (J'.over Q) AddCommGrpCat.{v} ⥤ Sheaf J' AddCommGrpCat.{v}}
    (adj : L ⊣ J'.overPullback AddCommGrpCat.{v} Q) :
    L.obj (characterTwist W' act' χ' (J'.over Q)) ≅
      characterTwist W'.left (forgetAut W' act') χ' J' :=
  characterTwistPushforwardIso (Over.forget Q) (J'.over Q) J' W' act' χ' adj

end Slice

end CategoryTheory

end
