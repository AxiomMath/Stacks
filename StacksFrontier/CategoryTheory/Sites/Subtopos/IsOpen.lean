module

public import StacksFrontier.CategoryTheory.Sites.Subtopos.Subtopoi
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Open subtopoi

Let `C` be a site and `F` a subsheaf of the final object of `Sh(C)`. The localization morphism
of topoi `j_F : Sh(C)/F ⟶ Sh(C)` (Stacks 04GZ) has inverse image `j_F⁻¹ = (H ↦ H × F / F)`,
which is Mathlib's `CategoryTheory.toOver F`, and pushforward `j_{F,*}`, a right adjoint of it.
By Stacks 08LW, `j_F` is an embedding of topoi, so `Sh(C)/F` is the subtopos of `Sh(C)` given by
the essential image of `j_{F,*}` (Stacks 08LV). Stacks 08LX calls a strictly full subcategory of
`Sh(C)` an *open subtopos* when it is this subtopos for some such `F`.

## Main definitions

* `IsOpenSubtopos`: a strictly full subcategory `P` of `Sh(C)` is an open subtopos when there
  is a subsheaf `F` of the final object such that `P` is the essential image of the
  pushforward `j_{F,*} : Sh(C)/F ⥤ Sh(C)` (Stacks 08LX).

## Main results

* `isOpenSubtopos_essImage`: for a subsheaf `F` of the final object, the essential image of
  `j_{F,*}` is an open subtopos.
* `IsOpenSubtopos.exists_forall_essImage_eq`: the subsheaf `F` presenting an open subtopos
  presents it through every choice of the right adjoint `j_{F,*}`.
* `isOpenSubtopos_iff_isEmbedding`: an open subtopos is the same as the essential image of the
  pushforward of a localization morphism `j_F` which is an embedding of topoi, i.e. exactly
  the subtopoi `Sh(C)/F` of Stacks 08LW.

## Implementation notes

* The pushforward `j_{F,*}` is quantified as data, an arbitrary right adjoint `p` of
  `toOver F`, as in `MorphismOfTopoi.overLocalization`. Right adjoints are unique up to natural
  isomorphism, and an essential image only depends on the functor up to natural isomorphism, so
  the choice does not matter (`IsOpenSubtopos.exists_forall_essImage_eq`); in `Sh(C)` such a
  right adjoint exists, the category being locally cartesian closed.
* This differs from `OpenSubtopos.IsOpenSubtopos`, which describes the essential image of
  `j_{F!} = Over.forget F`, the sheaves admitting a morphism to `F`. For the one-point site and
  `F` the initial sheaf, the essential image of `j_{F,*}` consists of the final sheaves while that
  of `j_{F!}` consists of the initial ones.
* "`F` is a subsheaf of the final object" is `CategoryTheory.IsSubterminal F`, as in Stacks 08LW.

Tags covered: 08LX.
-/

@[expose] public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/-- **Stacks Project, Definition 7.43.4 (tag 08LX).**

A strictly full subcategory `E ⊆ Sh(C, J)`, given by the property `P` of its objects, is an
*open subtopos* if there is a subsheaf `F` of the final object of `Sh(C, J)` such that `E` is
the subtopos `Sh(C, J)/F` of Stacks 08LW, that is, the essential image of the pushforward
`j_{F,*} : Sh(C, J)/F ⥤ Sh(C, J)` of the localization morphism `j_F`. Here `j_{F,*}` is a right
adjoint `p` of the pullback `j_F⁻¹ = toOver F : H ↦ (H × F ⟶ F)`. -/
@[stacks 08LX "A strictly full subcategory E of Sh(C) is an open subtopos if there is a subsheaf
F of the final object such that E is the essential image of the pushforward j_{F,*} of the
localization morphism j_F : Sh(C)/F → Sh(C), the right adjoint of H ↦ H × F / F."]
def IsOpenSubtopos (J : GrothendieckTopology C) (P : ObjectProperty (Sheaf J (Type w))) :
    Prop :=
  P.IsClosedUnderIsomorphisms ∧
  ∃ (F : Sheaf J (Type w)) (_ : IsSubterminal F) (p : Over F ⥤ Sheaf J (Type w))
    (_ : toOver F ⊣ p), p.essImage = P

variable {J : GrothendieckTopology C}

/-- For a subsheaf `F` of the final object, the essential image of the pushforward `j_{F,*}`
(any right adjoint of `toOver F`) is an open subtopos of `Sh(C, J)`. -/
theorem isOpenSubtopos_essImage {F : Sheaf J (Type w)} (hF : IsSubterminal F)
    {p : Over F ⥤ Sheaf J (Type w)} (adj : toOver F ⊣ p) :
    IsOpenSubtopos J p.essImage :=
  ⟨inferInstance, F, hF, p, adj, rfl⟩

/-- An open subtopos is the essential image of `j_{F,*}` for one subsheaf `F` of the final
object and *every* choice of the right adjoint `j_{F,*}` of `toOver F`. -/
theorem IsOpenSubtopos.exists_forall_essImage_eq {P : ObjectProperty (Sheaf J (Type w))}
    (h : IsOpenSubtopos J P) :
    ∃ F : Sheaf J (Type w), IsSubterminal F ∧
      ∀ (p : Over F ⥤ Sheaf J (Type w)) (_ : toOver F ⊣ p), p.essImage = P := by
  obtain ⟨-, F, hF, p₀, adj₀, rfl⟩ := h
  exact ⟨F, hF, fun p adj =>
    Functor.essImage_eq_of_natIso (Adjunction.rightAdjointUniq adj adj₀)⟩

/-- A strictly full subcategory of `Sh(C, J)` is an open subtopos if and only if it is the
essential image of the pushforward of a localization morphism `j_F : Sh(C, J)/F ⟶ Sh(C, J)`
which is an embedding of topoi: the open subtopoi are exactly the subtopoi `Sh(C, J)/F` of
Stacks 08LW. -/
theorem isOpenSubtopos_iff_isEmbedding (P : ObjectProperty (Sheaf J (Type w))) :
    IsOpenSubtopos J P ↔ P.IsClosedUnderIsomorphisms ∧
      ∃ (F : Sheaf J (Type w)) (p : Over F ⥤ Sheaf J (Type w)) (adj : toOver F ⊣ p),
        (MorphismOfTopoi.overLocalization F adj).IsEmbedding ∧
          (MorphismOfTopoi.overLocalization F adj).pushforward.essImage = P := by
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨F, hF, p, adj, hP⟩
    exact ⟨F, p, adj,
      (Sites.Subtopos.MorphismOfTopoi.isEmbedding_overLocalization_iff_isSubterminal F adj).2 hF,
      hP⟩
  · rintro ⟨F, p, adj, hE, hP⟩
    exact ⟨F,
      (Sites.Subtopos.MorphismOfTopoi.isEmbedding_overLocalization_iff_isSubterminal F adj).1 hE,
      p, adj, hP⟩
