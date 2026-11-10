module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.Examples.GroupSchemes.SectionCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two copies of a scheme glued along an open subscheme

Given a scheme `Y` and an open subscheme `U ⊆ Y`, glue two copies of `Y` along `U` by the
identity. The two copies are open immersions into the result which cover it, and both are
sections of the morphism to `Y` that restricts to the identity on each copy. The result is
therefore the total space of a `Stacks.Examples.SectionCoverData`, hence a group scheme over `Y`.

Its structure morphism is separated only if `U` is closed in `Y`: the fibre square of the second
copy over the first is the gluing locus `U`, so separatedness would make the inclusion of `U` a
closed immersion.

## Main definitions

* `Stacks.Examples.doublePreGlueData`, `Stacks.Examples.doubleGlueData`: the two-chart gluing
  datum whose off-diagonal overlap is `U` and whose transition map is the identity.
* `Stacks.Examples.doubleProjData`: the morphism to `Y` restricting to the identity on each
  copy, packaged with those equations.
* `Stacks.Examples.doubleSectionCover`: the resulting `SectionCoverData` over `Y`.

## Main results

* `Stacks.Examples.doubleSectionCover_not_isSeparated`: the structure morphism is not separated
  when `U` is not closed.

## Implementation notes

The charts are indexed by `ULift (Fin 2)`, since Mathlib's scheme gluing datum places its index
type in the same universe as the schemes, while the two labels of a `SectionCoverData` are
indexed by `Bool`; `Stacks.Examples.doubleIndex` mediates. Both copies are the same scheme, so
the identification on the overlap is literally the identity morphism, and the auxiliary
`CategoryTheory.GlueData'` form makes the cocycle condition vacuous because three pairwise
distinct labels do not exist.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Examples

/-- Auxiliary gluing data for two copies of `Y`, in which only the off-diagonal intersection is
specified: it is the open subscheme `U`, included in either copy in the standard way. -/
@[ega "IV 20.2.16"]
public noncomputable def doublePreGlueData (Y : Scheme.{u}) (V : Y.Opens) :
    CategoryTheory.GlueData' Scheme.{u} where
  J := ULift.{u} (Fin 2)
  U _ := Y
  V _ _ _ := V.toScheme
  f _ _ _ := V.ι
  f_hasPullback := by intros; infer_instance
  t _ _ _ := 𝟙 _
  t' i j l hij hil hjl := by
    exfalso; obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨l⟩ := l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  t_fac i j l hij hil hjl := by
    exfalso; obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨l⟩ := l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  t_inv := by intros; simp
  cocycle i j l hij hil hjl := by
    exfalso; obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨l⟩ := l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

/-- The gluing datum for two copies of `Y` identified along the open subscheme `V` by the
identity. -/
@[ega "IV 20.2.16", sga "6 II AppI.1.2"]
public noncomputable def doubleGlueData (Y : Scheme.{u}) (V : Y.Opens) : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (doublePreGlueData Y V)
  f_open i j := by
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      doublePreGlueData]
    split_ifs <;> infer_instance

/-- The two chart labels, as indices of the gluing datum. -/
public def doubleIndex (Y : Scheme.{u}) (V : Y.Opens) : Bool ≃ (doubleGlueData Y V).J :=
  finTwoEquiv.symm.trans Equiv.ulift.symm

/-- The morphism from two copies of `Y` glued along `V` to `Y`, restricting to the identity on
each copy, packaged with those equations. -/
@[ega "IV 20.2.16", sga "7 VIII 5.7" "special case"]
public noncomputable def doubleProjData (Y : Scheme.{u}) (V : Y.Opens) :
    { f : (doubleGlueData Y V).glued ⟶ Y //
      ∀ i : (doubleGlueData Y V).J, (doubleGlueData Y V).ι i ≫ f = 𝟙 Y } := by
  classical
  let D := doubleGlueData Y V
  have hcompat : ∀ a : D.toGlueData.J × D.toGlueData.J,
      D.toGlueData.diagram.fst a ≫ (fun _ => 𝟙 _) _ =
        D.toGlueData.diagram.snd a ≫ (fun _ => 𝟙 _) _ := by
    rintro ⟨i, j⟩
    change D.f i j ≫ 𝟙 _ = D.t i j ≫ D.f j i ≫ 𝟙 _
    obtain ⟨i⟩ := i; obtain ⟨j⟩ := j
    fin_cases i <;> fin_cases j <;>
      simp [D, doubleGlueData, GlueData.ofGlueData', doublePreGlueData, GlueData'.f']
  exact ⟨Multicoequalizer.desc D.toGlueData.diagram _ (fun _ => 𝟙 _) hcompat,
    Multicoequalizer.π_desc D.toGlueData.diagram Y (fun _ => 𝟙 _) hcompat⟩

/-- Two copies of `Y` glued along the open subscheme `V`, with its two copies as the two
sections of its structure morphism. -/
@[sga "7 VIII 5.7" "special case"]
public noncomputable def doubleSectionCover (Y : Scheme.{u}) (V : Y.Opens) :
    SectionCoverData Y where
  total := (doubleGlueData Y V).glued
  proj := (doubleProjData Y V).1
  chart b := (doubleGlueData Y V).ι (doubleIndex Y V b)
  chart_comp_proj b := (doubleProjData Y V).2 _
  isOpenImmersion_chart b := Scheme.GlueData.ι_isOpenImmersion _ _
  exists_chart_eq x := by
    obtain ⟨i, y, hy⟩ := (doubleGlueData Y V).ι_jointly_surjective x
    obtain ⟨b, rfl⟩ := (doubleIndex Y V).surjective i
    exact ⟨b, y, hy⟩

/-- The chart of `doubleSectionCover Y V` at `b` is the gluing inclusion of the `b`-th copy
of `Y`. -/
public lemma doubleSectionCover_chart (Y : Scheme.{u}) (V : Y.Opens) (b : Bool) :
    (doubleSectionCover Y V).chart b = (doubleGlueData Y V).ι (doubleIndex Y V b) := rfl

/-- The structure morphism of `doubleSectionCover Y V` is the morphism to `Y` induced by the
identities on the two copies. -/
public lemma doubleSectionCover_proj (Y : Scheme.{u}) (V : Y.Opens) :
    (doubleSectionCover Y V).proj = (doubleProjData Y V).1 := rfl

/-- For two distinct labels, the overlap map of the gluing datum is the inclusion of `V`,
precomposed with the isomorphism identifying the overlap with `V`. -/
public lemma doubleGlueData_f_eq_comp (Y : Scheme.{u}) (V : Y.Opens) {b c : Bool} (h : b ≠ c) :
    (doubleGlueData Y V).f (doubleIndex Y V b) (doubleIndex Y V c) =
      eqToHom (dite_eq_right ((doubleIndex Y V).injective.ne h)) ≫ V.ι :=
  dite_eq_right ((doubleIndex Y V).injective.ne h)

/-- Up to an isomorphism, the off-diagonal overlap map of the gluing datum is the inclusion
of `V`. -/
public lemma doubleGlueData_f_isClosedImmersion_iff (Y : Scheme.{u}) (V : Y.Opens)
    {b c : Bool} (h : b ≠ c) :
    IsClosedImmersion ((doubleGlueData Y V).f (doubleIndex Y V b) (doubleIndex Y V c)) ↔
      IsClosedImmersion V.ι := by
  rw [doubleGlueData_f_eq_comp Y V h]
  exact MorphismProperty.cancel_left_of_respectsIso _ _ _

/-- The transition map of the gluing datum, composed with the cast back from the
identification of the overlap with `V`, equals the cast in from `V` on the other side.

The proof unfolds the `dite` defining `(doubleGlueData Y V).t` directly in the goal (via `show`
and `dif_neg`), rather than rewriting by a separately-stated bridge lemma: `rw`/`simp`'s pattern
matching cannot see through the non-reducible `doubleGlueData`/`GlueData.ofGlueData'` to
identify `(doubleGlueData Y V).J` with `(doublePreGlueData Y V).J`, so a rewrite whose pattern
is stated against `doublePreGlueData Y V` fails to match a goal stated against
`doubleGlueData Y V`, even though the two are definitionally equal. -/
public lemma doubleGlueData_t_comp_eqToHom (Y : Scheme.{u}) (V : Y.Opens) {b c : Bool}
    (h : b ≠ c) :
    (doubleGlueData Y V).t (doubleIndex Y V b) (doubleIndex Y V c) ≫
      eqToHom (dite_eq_right ((doubleIndex Y V).injective.ne h.symm)) =
      eqToHom (dite_eq_right ((doubleIndex Y V).injective.ne h)) := by
  classical
  have hbc := (doubleIndex Y V).injective.ne h
  change (if hh : (doubleIndex Y V) b = (doubleIndex Y V) c then eqToHom (by simp [hh])
      else eqToHom (dite_eq_right hh) ≫ (doublePreGlueData Y V).t (doubleIndex Y V b)
        (doubleIndex Y V c) hh ≫ eqToHom (dite_eq_right (Ne.symm hh)).symm) ≫
      eqToHom (dite_eq_right hbc.symm) = eqToHom (dite_eq_right hbc)
  have hDt : (doublePreGlueData Y V).t (doubleIndex Y V b) (doubleIndex Y V c) hbc =
      eqToHom (show (doublePreGlueData Y V).V (doubleIndex Y V b) (doubleIndex Y V c) hbc =
        (doublePreGlueData Y V).V (doubleIndex Y V c) (doubleIndex Y V b) (Ne.symm hbc) from
        rfl) :=
    rfl
  rw [dite_eq_right hbc]
  rw [hDt]
  simp only [eqToHom_trans]
  rfl

/-- **The two charts of the glued scheme meet exactly in the gluing locus.** For two distinct
labels the fibre product of the two charts over the glued scheme is the open subscheme `V`,
included in either copy of `Y` in the standard way.

This is `CategoryTheory.GlueData.vPullbackConeIsLimit` for the two labels, in which both legs
become the inclusion of `V`: the first is the overlap map, which is that inclusion up to the
identification of the overlap with `V` (`doubleGlueData_f_eq_comp`), and the second is the
transition map followed by the opposite overlap map, which is the same because the transition
map is the identity (`doubleGlueData_t_comp_eqToHom`). The common identification of the overlap
with `V` is then an isomorphism of the corner, which `CategoryTheory.IsPullback.of_iso`
removes. -/
@[ega "IV 20.2.16" "partial", sga "6 II AppI.1.2" "partial"]
public theorem doubleSectionCover_isPullback_chart (Y : Scheme.{u}) (V : Y.Opens) {b c : Bool}
    (h : b ≠ c) :
    IsPullback V.ι V.ι ((doubleSectionCover Y V).chart b) ((doubleSectionCover Y V).chart c) := by
  have hp : IsPullback ((doubleGlueData Y V).f (doubleIndex Y V b) (doubleIndex Y V c))
      ((doubleGlueData Y V).t (doubleIndex Y V b) (doubleIndex Y V c) ≫
        (doubleGlueData Y V).f (doubleIndex Y V c) (doubleIndex Y V b))
      ((doubleGlueData Y V).ι (doubleIndex Y V b))
      ((doubleGlueData Y V).ι (doubleIndex Y V c)) :=
    IsPullback.of_isLimit ((doubleGlueData Y V).vPullbackConeIsLimit
      (doubleIndex Y V b) (doubleIndex Y V c))
  rw [doubleGlueData_f_eq_comp Y V h, doubleGlueData_f_eq_comp Y V h.symm] at hp
  -- `t ≫ eqToHom _ ≫ V.ι = eqToHom _ ≫ V.ι`, flattened from `doubleGlueData_t_comp_eqToHom`
  -- forward through `Category.assoc` applied as a term
  have hinner := congrArg (· ≫ V.ι) (doubleGlueData_t_comp_eqToHom Y V h)
  have hsecond := (Category.assoc _ _ _).symm.trans hinner
  simp only [doubleSectionCover_chart]
  exact hp.of_iso (eqToIso (dite_eq_right ((doubleIndex Y V).injective.ne h)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Category.comp_id _)
    ((Category.comp_id _).trans hsecond)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The defining gluing relation.** The two charts of the glued scheme agree after
composing with the inclusion of the gluing locus: this is the commutativity of the square
`doubleSectionCover_isPullback_chart`. -/
public theorem doubleSectionCover_chart_agree (Y : Scheme.{u}) (V : Y.Opens) :
    V.ι ≫ (doubleSectionCover Y V).chart true = V.ι ≫ (doubleSectionCover Y V).chart false :=
  (doubleSectionCover_isPullback_chart Y V (b := true) (c := false) (by decide)).w

/-- Two copies of `Y` glued along an open subscheme that is not closed give a scheme whose
structure morphism to `Y` is not separated. -/
@[ega "IV 20.2.16" "partial"]
public theorem doubleSectionCover_not_isSeparated (Y : Scheme.{u}) (V : Y.Opens)
    (hV : ¬ IsClosed (V : Set Y)) : ¬ IsSeparated (doubleSectionCover Y V).proj := by
  intro hsep
  have := hsep
  have h₁ : IsClosedImmersion
      ((doubleSectionCover Y V).chart true ≫ (doubleSectionCover Y V).proj) := by
    rw [(doubleSectionCover Y V).chart_comp_proj]
    infer_instance
  have h₂ : IsClosedImmersion ((doubleSectionCover Y V).chart true) :=
    IsClosedImmersion.of_comp _ (doubleSectionCover Y V).proj
  have hp := IsPullback.of_isLimit ((doubleGlueData Y V).vPullbackConeIsLimit
    (doubleIndex Y V false) (doubleIndex Y V true))
  have h₃ : IsClosedImmersion
      ((doubleGlueData Y V).f (doubleIndex Y V false) (doubleIndex Y V true)) :=
    MorphismProperty.of_isPullback hp.flip h₂
  have h₄ : IsClosedImmersion V.ι :=
    (doubleGlueData_f_isClosedImmersion_iff Y V (by simp)).mp h₃
  exact hV (by simpa using (Scheme.Hom.isClosedEmbedding V.ι).isClosed_range)

end Stacks.Examples

end
