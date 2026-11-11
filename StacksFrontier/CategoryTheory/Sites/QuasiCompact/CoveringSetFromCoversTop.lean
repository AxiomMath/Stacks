module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects

/-!
# Checking the hypotheses of Stacks 0GMS case (2) against site-level data, and 0GMS case (3)

`CategoryTheory.Sheaf.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self` is Stacks
0GMS case (2): a set `B` of objects of a site satisfying three conditions (a), (b), (c) produces
the hypothesis of Stacks 0GMR part (4). Conditions (a) and (c) are stated there in terms of
surjections of sheaves of sets. This file supplies them from purely site-theoretic data:
`CategoryTheory.GrothendieckTopology.CoversTop` for (a), and a covering arrow into a categorical
product of the site for (c).

## Main results

* `forall_exists_mem_coveringSetOfObjects_and_isQuasiCompact_prod_self_of_isQuasiCompactTopos`:
  **Stacks 0GMS case (3)** — the set of finite coproducts of `h_U^#` for quasi-compact `U`
  satisfies the hypotheses of Stacks 0GMR (4) on a site satisfying (3)(a), (3)(b), (3)(c).
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

The one `@[stacks]` attribute here is `@[stacks 0GMS "case (3)"]`, placed in this file because
its proof covers the final object with `CoversTop` through
`isLocallySurjective_terminal_from_sigma_sheafifiedYoneda`. Cases (1) and (2) of Stacks 0GMS have
their sites in `StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects`; the other
results here are inputs for checking case (2) and are not separate assertions of the source.

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

/-! ### Stacks 0GMS case (3) -/

/-- **Stacks 0GMS, case (3).** Let `C` be a site such that

* (a) `Sh(C)` is quasi-compact (Stacks 0D07),
* (b) every object of `C` has a covering whose members are quasi-compact objects (Stacks 090H),
* (c) if `U` and `U'` are quasi-compact objects then the sheaf `h_U^# ⨯ h_{U'}^#` is
  quasi-compact.

Then the hypotheses of part (4) of Stacks 0GMR are satisfied by the set `S` of finite coproducts of
the sheaves `h_U^#` for `U` a quasi-compact object of `C`, which is
`CategoryTheory.Sheaf.coveringSetOfObjects J {U | J.IsQuasiCompactObject U}`: every sheaf of sets
`G` surjecting onto the final sheaf receives a morphism from a member `K` of `S` with `K ⟶ *`
surjective, and `K ⨯ K` is quasi-compact for every `K ∈ S`.

The source states this without proof. *Proof.* For (4)(b), (c) is hypothesis (1)(b) of the remark
for the set of quasi-compact objects, and
`CategoryTheory.Sheaf.isQuasiCompact_prod_self_of_mem_coveringSetOfObjects` applies. For (4)(a),
let `G ⟶ *` be surjective and index a family by the pairs `(U, s)` with `U` quasi-compact and
`s ∈ G(U)`. These objects cover the final object: every object `W` has a covering on whose members
`G` has a section, each member has a covering by quasi-compact objects by (b), and `G` has
sections over these by restriction. So `∐_{(U, s)} h_U^# ⟶ *` is surjective
(`isLocallySurjective_terminal_from_sigma_sheafifiedYoneda`); by (a) a finite subfamily is
already surjective, its coproduct `K` lies in `S`, and the sections `s` give `K ⟶ G`. -/
@[stacks 0GMS "case (3)"]
theorem forall_exists_mem_coveringSetOfObjects_and_isQuasiCompact_prod_self_of_isQuasiCompactTopos
    (ha : J.IsQuasiCompactTopos)
    (hb : ∀ W : C, ∃ 𝒰 : PreZeroHypercover.{max u v} W,
      𝒰.sieve₀ ∈ J W ∧ ∀ i, J.IsQuasiCompactObject (𝒰.X i))
    (hc : ∀ U U' : C, J.IsQuasiCompactObject U → J.IsQuasiCompactObject U' →
      IsQuasiCompact ((sheafifiedYoneda J).obj U ⨯ (sheafifiedYoneda J).obj U')) :
    (∀ G : Sheaf J (Type max u v), IsLocallySurjective (terminal.from G) →
        ∃ K ∈ coveringSetOfObjects J {U | J.IsQuasiCompactObject U}, Nonempty (K ⟶ G) ∧
          IsLocallySurjective (terminal.from K)) ∧
      ∀ K ∈ coveringSetOfObjects J {U | J.IsQuasiCompactObject U}, IsQuasiCompact (K ⨯ K) := by
  refine ⟨fun G hG => ?_, fun K hK =>
    isQuasiCompact_prod_self_of_mem_coveringSetOfObjects (fun W hW W' hW' => hc W W' hW hW') hK⟩
  let Y : (Σ U : {U : C // J.IsQuasiCompactObject U}, G.obj.obj (op U.1)) → C := fun p => p.1.1
  have hY : J.CoversTop Y := by
    intro W
    obtain ⟨T, hT, hTsec⟩ := exists_covering_nonempty_section hG W
    refine J.transitive hT _ fun V g hg => ?_
    rw [Sieve.pullback_ofObjects]
    obtain ⟨t⟩ := hTsec g hg
    obtain ⟨𝒰, h𝒰, hqc⟩ := hb V
    refine J.superset_covering (fun Z a ha => ?_) h𝒰
    obtain ⟨k, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ha
    exact ⟨⟨⟨𝒰.X k, hqc k⟩, G.obj.map (𝒰.f k).op t⟩, ⟨b⟩⟩
  have hsurj := isLocallySurjective_terminal_from_sigma_sheafifiedYoneda J Y hY
  have hdesc : terminal.from (∐ fun p => (sheafifiedYoneda J).obj (Y p)) =
      Sigma.desc fun p => terminal.from ((sheafifiedYoneda J).obj (Y p)) :=
    terminal.hom_ext _ _
  rw [hdesc] at hsurj
  obtain ⟨T, hT, hTsurj⟩ := ha _ _ _ hsurj
  have : Finite T := hT.to_subtype
  refine ⟨∐ fun j : T => (sheafifiedYoneda J).obj (Y j.1),
    ⟨T, inferInstance, fun j => Y j.1, fun j => j.1.1.2, rfl⟩,
    ⟨Sigma.desc fun j => (sectionEquiv J).symm j.1.2⟩, ?_⟩
  have hdesc' : terminal.from (∐ fun j : T => (sheafifiedYoneda J).obj (Y j.1)) =
      Sigma.desc fun j : T => terminal.from ((sheafifiedYoneda J).obj (Y j.1)) :=
    terminal.hom_ext _ _
  rw [hdesc']
  exact hTsurj

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
