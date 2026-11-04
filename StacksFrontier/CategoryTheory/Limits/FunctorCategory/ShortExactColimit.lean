module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Short exactness in a functor category, and its colimits

Let `A` be an abelian category and `D` a category. A short complex of functors `D ⥤ A` is exact,
or short exact, as soon as it is so at every object of `D`: the evaluation functors are exact and
jointly reflect isomorphisms. Combining this with the exactness of `D`-shaped colimits in `A`
gives the statement this file exists for: the colimit of a short exact sequence of functors
`D ⥤ A` is a short exact sequence in `A`, for arbitrary colimit cocones over the three terms.

## Main results

* `CategoryTheory.jointlyReflectIsomorphisms_evaluation`: the evaluation functors of a functor
  category jointly reflect isomorphisms.
* `CategoryTheory.ShortComplex.exact_of_app` and
  `CategoryTheory.ShortComplex.shortExact_of_app`: objectwise exactness, respectively objectwise
  short exactness, of a short complex of functors implies exactness, respectively short
  exactness.
* `CategoryTheory.Limits.colim.shortExact_mapShortComplex`: **the colimit of an objectwise short
  exact sequence of functors `D ⥤ A` is short exact**, when `D`-shaped colimits in `A` are
  exact.

## Implementation notes

The hypothesis of the colimit statement is objectwise short exactness rather than short
exactness in `D ⥤ A`. The two are equivalent, by `shortExact_of_app` and because evaluation is
exact, but the objectwise form is what consumers have and it is what the three conclusions
consume: `Limits.colim.map_epi'` asks for objectwise epimorphisms directly, and the
monomorphism is obtained from the objectwise ones through `NatTrans.mono_of_mono_app`.

Arbitrary colimit cocones are allowed rather than the ones of the colimit API, matching
`Limits.colim.mapShortComplex`; a consumer whose colimits come from an explicit construction —
a cofan of direct summands, say — then needs no comparison isomorphism.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits

variable {D : Type w} [Category.{w'} D] {A : Type u} [Category.{v} A]

/-- The evaluation functors of a functor category jointly reflect isomorphisms: a natural
transformation which is an isomorphism at every object is an isomorphism. -/
lemma jointlyReflectIsomorphisms_evaluation :
    JointlyReflectIsomorphisms (fun d : D ↦ (evaluation D A).obj d) :=
  ⟨fun f h ↦ by
    have : ∀ d : D, IsIso (f.app d) := h
    exact NatIso.isIso_of_isIso_app f⟩

variable [Abelian A]

/-- A short complex of functors which is exact at every object of the source category is
exact. -/
lemma ShortComplex.exact_of_app (S : ShortComplex (D ⥤ A))
    (h : ∀ d : D, (S.map ((evaluation D A).obj d)).Exact) : S.Exact :=
  (jointlyReflectIsomorphisms_evaluation.exact_iff S).2 h

/-- A short complex of functors which is short exact at every object of the source category is
short exact. -/
@[sga "3 I 5.2" "partial"]
lemma ShortComplex.shortExact_of_app (S : ShortComplex (D ⥤ A))
    (h : ∀ d : D, (S.map ((evaluation D A).obj d)).ShortExact) : S.ShortExact :=
  (jointlyReflectIsomorphisms_evaluation.shortExact_iff S).2 h

namespace Limits

variable [HasColimitsOfShape D A] [HasExactColimitsOfShape D A] {S : ShortComplex (D ⥤ A)}
  (hS : ∀ d : D, (S.map ((evaluation D A).obj d)).ShortExact)
  {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) {c₂ : Cocone S.X₂} (hc₂ : IsColimit c₂)
  {c₃ : Cocone S.X₃} (hc₃ : IsColimit c₃) (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
  (hf : ∀ d : D, c₁.ι.app d ≫ f = S.f.app d ≫ c₂.ι.app d)
  (hg : ∀ d : D, c₂.ι.app d ≫ g = S.g.app d ≫ c₃.ι.app d)

include hS hc₂ hc₃ in
/-- **The colimit of an objectwise short exact sequence of functors `D ⥤ A` is short exact**,
provided `D`-shaped colimits in `A` are exact. The three colimit cocones are arbitrary, and the
maps between their points are only required to be compatible with the sequence. -/
lemma colim.shortExact_mapShortComplex :
    (colim.mapShortComplex S hc₁ c₂ c₃ f g hf hg).ShortExact := by
  have hmono : ∀ d : D, Mono (S.f.app d) := fun d ↦ (hS d).mono_f
  have : Mono S.f := NatTrans.mono_of_mono_app _
  have hepi : ∀ d : D, Epi (S.g.app d) := fun d ↦ (hS d).epi_g
  exact ShortComplex.ShortExact.mk'
    (colim.exact_mapShortComplex (ShortComplex.exact_of_app S fun d ↦ (hS d).exact)
      hc₁ hc₂ hc₃ f g hf hg)
    (colim.map_mono' S.f hc₁ hc₂ f hf) (colim.map_epi' S.g c₂ hc₃ g hg)

end Limits

end CategoryTheory
