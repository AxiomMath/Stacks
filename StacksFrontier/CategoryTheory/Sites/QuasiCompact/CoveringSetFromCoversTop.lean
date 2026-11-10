module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects

/-!
# Checking the hypotheses of Stacks 0GMS case (2) against site-level data

`CategoryTheory.Sheaf.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self` is Stacks
0GMS case (2): a set `B` of objects of a site satisfying three conditions (a), (b), (c) produces
the hypothesis of Stacks 0GMR part (4). Conditions (a) and (c) are stated there in terms of
surjections of sheaves of sets. This file supplies them from purely site-theoretic data:
`CategoryTheory.GrothendieckTopology.CoversTop` for (a), and a covering arrow into a categorical
product of the site for (c).

## Main results

* `CategoryTheory.Sheaf.isLocallySurjective_terminal_from_sigma_sheafifiedYoneda`: a family of
  objects covering the final object makes `∐_i h_{U_i}^# ⟶ *` a surjection of sheaves. This is
  condition (a) of Stacks 0GMS case (2).
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_mem`: a covering arrow
  `W ⟶ U ⨯ U'` makes `h_W^# ⟶ h_U^# ⨯ h_{U'}^#` a surjection of sheaves. This is condition (c)
  of Stacks 0GMS case (2) for a one-element family.
* `CategoryTheory.Sheaf.preservesFiniteLimits_sheafifiedYoneda`: the sheafified Yoneda embedding
  commutes with finite limits, which is what turns a product of objects of the site into a
  product of sheaves.

## Implementation notes

No `@[stacks]` attribute is carried: Stacks 0GMS is a remark whose case (2) already has its
single site on `exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`, and nothing here
is a separate assertion of the source.

The terminal sheaf of sets has subsingleton sections over every object, which is what makes
condition (a) follow from `CoversTop` with no computation: a morphism into the terminal sheaf is
unique, and `CategoryTheory.Sheaf.sectionEquiv` identifies the sections over an object with the
morphisms out of the sheafified representable. This is recorded as
`subsingleton_terminalSheaf_obj` and is a `theorem` rather than an `instance`, since it would
otherwise be tried on every subsingleton goal about sections of a sheaf.

Nothing here hypothesizes sheafification: Mathlib supplies `HasSheafify J (Type max u v)` on
every site. Adding it as a local hypothesis instead makes instance search for coproducts in the
sheaf category diverge, so it is deliberately absent.

## References

* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 00WT](https://stacks.math.columbia.edu/tag/00WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-! ### Conditions (a) and (c) of Stacks 0GMS case (2) from site-level data -/

namespace Sheaf

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The coproduct of a family of sheafified representables, as an instance matching that shape
directly. Instance search for it from scratch diverges in any file importing
`Mathlib.CategoryTheory.Sites.Equivalence`, whose `hasColimitsEssentiallySmallSite` fires on
every colimit goal in a sheaf category; this records the answer once. -/
noncomputable instance hasColimit_discrete_sheafifiedYoneda {ι : Type max u v} (U : ι → C) :
    HasColimit (Discrete.functor fun i => (sheafifiedYoneda J).obj (U i)) := inferInstance

/-- Sections of the terminal sheaf of sets over an object form a subsingleton: they are the
morphisms from the sheafified representable into a terminal object. -/
theorem subsingleton_terminalSheaf_obj (V : C) :
    Subsingleton ((⊤_ (Sheaf J (Type max u v))).obj.obj (op V)) :=
  have : Subsingleton ((sheafifiedYoneda J).obj V ⟶ ⊤_ (Sheaf J (Type max u v))) :=
    ⟨fun f g => terminal.hom_ext f g⟩
  (sectionEquiv J (X := V) (F := ⊤_ (Sheaf J (Type max u v)))).symm.subsingleton

/-- **Condition (a) of Stacks 0GMS case (2) from `CoversTop`.** If a family of objects of the
site covers the final object, then the induced morphism `∐_i h_{U_i}^# ⟶ *` is a surjection of
sheaves of sets.

An object through which some `U i` is reached carries a section of `∐_i h_{U_i}^#`, namely the
image of the corresponding morphism under `CategoryTheory.Sheaf.sectionEquiv` followed by a
coprojection; and the condition to be a preimage is vacuous, the target being terminal. -/
theorem isLocallySurjective_terminal_from_sigma_sheafifiedYoneda {ι : Type max u v} (U : ι → C)
    (hU : J.CoversTop U) :
    IsLocallySurjective (terminal.from (∐ fun i => (sheafifiedYoneda J).obj (U i))) := by
  refine ⟨fun {W} _ => J.superset_covering (fun V g hg => ?_) (hU W)⟩
  obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff U g).1 hg
  exact ⟨sectionEquiv J ((sheafifiedYoneda J).map b ≫
      Sigma.ι (fun i => (sheafifiedYoneda J).obj (U i)) i),
    (subsingleton_terminalSheaf_obj J V).elim _ _⟩

/-- **The sheafified Yoneda embedding commutes with finite limits**, being the composite of the
universe-lifted Yoneda embedding with sheafification. -/
theorem preservesFiniteLimits_sheafifiedYoneda :
    PreservesFiniteLimits (sheafifiedYoneda J) :=
  have _ : PreservesFiniteLimits (uliftYoneda.{u, v, u} (C := C)) := inferInstance
  have _ : PreservesFiniteLimits (presheafToSheaf J (Type max u v)) := inferInstance
  comp_preservesFiniteLimits _ _

variable [HasBinaryProducts C]

/-- The comparison `h_{U ⨯ U'}^# ⟶ h_U^# ⨯ h_{U'}^#` is an isomorphism. -/
theorem isIso_prodComparison_sheafifiedYoneda (U U' : C) :
    IsIso (prodComparison (sheafifiedYoneda J) U U') :=
  have _ := preservesFiniteLimits_sheafifiedYoneda J
  have _ : PreservesLimit (pair U U') (sheafifiedYoneda J) := inferInstance
  inferInstance

/-- **Condition (c) of Stacks 0GMS case (2) for a one-element family.** If `p : W ⟶ U ⨯ U'`
generates a covering sieve of the categorical product, then the induced morphism
`h_W^# ⟶ h_U^# ⨯ h_{U'}^#` is a surjection of sheaves of sets.

The displayed morphism is `h_p^#` followed by the product comparison of the sheafified Yoneda
embedding, which is invertible because that functor commutes with finite limits; and `h_p^#` is
a surjection by Stacks 00WT. -/
theorem isLocallySurjective_sigmaDesc_prodLift_of_mem {ι : Type max u v}
    {U U' W : C} (p : W ⟶ U ⨯ U')
    (hp : Sieve.ofArrows (fun _ : ι => W) (fun _ => p) ∈ J (U ⨯ U')) :
    IsLocallySurjective (Sigma.desc fun _ : ι =>
      prod.lift ((sheafifiedYoneda J).map (p ≫ prod.fst))
        ((sheafifiedYoneda J).map (p ≫ prod.snd))) := by
  have hfac : (Sigma.desc fun _ : ι => (sheafifiedYoneda J).map p) ≫
      prodComparison (sheafifiedYoneda J) U U' =
      Sigma.desc fun _ : ι =>
        prod.lift ((sheafifiedYoneda J).map (p ≫ prod.fst))
          ((sheafifiedYoneda J).map (p ≫ prod.snd)) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc, prodComparison, prod.comp_lift,
      ← Functor.map_comp, ← Functor.map_comp]
  have _ : IsLocallySurjective (Sigma.desc fun _ : ι => (sheafifiedYoneda J).map p) :=
    (Stacks.Sites.QuasiCompactCriterion.isLocallySurjective_sigmaDesc_sheafifiedYoneda_map_iff
      (J := J) (fun _ : ι => p)).2 hp
  have _ := isIso_prodComparison_sheafifiedYoneda J U U'
  exact hfac ▸ inferInstance

end Sheaf

end CategoryTheory

end
