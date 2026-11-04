module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a coproduct of sheaves of sets over a quasi-compact object

Let `C` be a site and let `W` be a quasi-compact object of `C` (Stacks 090H). Part (1) of
Stacks 0935 asserts that the sections functor `Sh(C) → Sets`, `F ↦ F(W)`, commutes with
coproducts, and its proof is a reduction: an arbitrary coproduct `∐_{i ∈ I} F_i` of sheaves of
sets is the filtered colimit, over the poset of finite subsets `E ⊆ I`, of the finite
sub-coproducts `F_E = ∐_{i ∈ E} F_i`; the transition maps of that diagram are injective; so
Stacks 0738 part (3) computes the sections of the colimit over a quasi-compact object.

That reduction is carried out here, with the filtered presentation and the injectivity of its
transition maps constructed rather than assumed:

* the presentation is Mathlib's `CategoryTheory.Limits.CoproductsFromFiniteFiltered`:
  `liftToFinsetObj (Discrete.functor f)` is the diagram `E ↦ ∐_{i ∈ E} F_i` on `Finset I`,
  which is a filtered poset, and `isColimitFiniteSubproductsCocone` identifies its colimit with
  `∐_{i ∈ I} F_i`;
* the transition map attached to `E ⊆ E'` is the map of coproducts along an injection of index
  types, so it is a monomorphism because coproduct injections in `Sh(C)` are
  (`CategoryTheory.Limits.MonoCoprod`, available because a sheaf topos is finitary extensive);
* Stacks 0738 part (3) is
  `CategoryTheory.Sheaf.injective_and_bijective_colimit_post_sheafSections`.

## The finite case, and part (1) as stated, are false

The step the source's proof leaves implicit — that sections over `W` commute with *finite*
coproducts of sheaves of sets — does not hold, and neither does part (1). Two failures, in
increasing order of substance.

*The empty coproduct.* If the empty sieve covers `W` then every sheaf has exactly one section
over `W` (`CategoryTheory.Sheaf.isTerminalOfBotCover`), while the empty coproduct of sets is
empty; and such a `W` is quasi-compact, since the empty family refines every covering through a
map with empty image. This is not an artefact of exotic sites: in the site of opens of any
topological space the empty open is such an object, which is
`not_preservesColimitsOfShape_pempty_sheafSections_opens_bot` below.

*Binary coproducts, with `W` nonempty.* Sections over a quasi-compact object commute with
binary coproducts only when `W` is connected. If `W` carries a covering by two monomorphisms
whose overlaps are covered by the empty sieve, then `F(W) = F(V₀) × F(V₁)` for every sheaf `F`
(`CategoryTheory.Presheaf.IsSheaf.isLimitFanSectionsOfDisjointArrows`), a *product* of the
sections of the two pieces and not a coproduct of anything. Concretely, on the two-point
discrete space `X`, the whole space is a quasi-compact object of `Opens X`, the coproduct
`⊤ ⊔ ⊤` of two copies of the terminal sheaf is the sheaf of locally constant maps to a
two-element set, and it has four sections over `X` where `⊤(X) ⊔ ⊤(X)` has two. The correct
statement — SGA 4 VI 1.23, which is also what `Stacks 0738` records — is that sections over a
quasi-compact object commute with filtered colimits with injective transition maps; the
coproduct form additionally needs `W` connected.

Part (2) of the source, sections of sheaves of modules over a quasi-compact object and direct
sums, is unaffected by any of this and is carried by
`Stacks.Sites.sheafOfModules_sections_preserves_coproducts`: a *finite* direct sum of abelian
sheaves is a finite product, hence commutes with sections over every object by Stacks 03CO.

## Main results

* `Stacks.Sites.mono_liftToFinsetObj_map`: the transition maps of the finite-sub-coproduct
  diagram of a family of sheaves of sets are monomorphisms.
* `Stacks.Sites.bijective_colimit_post_liftToFinsetObj`: over a quasi-compact object, the
  canonical map from the colimit of the sections of the finite sub-coproducts to the sections of
  the coproduct is bijective.
* `Stacks.Sites.isColimitSectionsFiniteSubcoproductsCocone`: the same statement as the
  assertion that sections over a quasi-compact object carry the finite-sub-coproduct
  presentation of `∐_{i ∈ I} F_i` to a colimit in `Sets`.
* `Stacks.Sites.isQuasiCompactObject_of_bot_mem`,
  `Stacks.Sites.not_preservesColimitsOfShape_pempty_of_bot_mem` and
  `Stacks.Sites.not_preservesColimitsOfShape_pempty_sheafSections_opens_bot`: part (1) of the
  source, as stated, is false.

## References

* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

universe w₂ w₁ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CoproductsFromFiniteFiltered
  Opposite TopologicalSpace

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### The filtered presentation by finite sub-coproducts -/

/-- **The transition maps of the finite-sub-coproduct diagram are monomorphisms.** For `E ⊆ E'`
finite subsets of the index type of a family `f` of sheaves of sets, the induced map
`∐_{i ∈ E} f i ⟶ ∐_{i ∈ E'} f i` is a monomorphism: it is the map of coproducts along an
injection of index types, and coproduct injections in a sheaf topos are monomorphisms. -/
theorem mono_liftToFinsetObj_map {ι : Type max u v} (f : ι → Sheaf J (Type max u v))
    (S T : Finset (Discrete ι)) (h : S ⟶ T) :
    Mono ((liftToFinsetObj (Discrete.functor f)).map h) := by
  have hinj : Function.Injective
      (fun y : {x // x ∈ S} => (⟨y.1, h.down.down y.2⟩ : {x // x ∈ T})) :=
    fun _ _ hy => Subtype.ext (congrArg Subtype.val hy :)
  exact MonoCoprod.mono_of_injective' (fun x : {x // x ∈ T} => (Discrete.functor f).obj x) _ hinj

/-- **The reduction of Stacks 0935 part (1) to the finite case.** Let `W` be a quasi-compact
object of a site and let `f` be a family of sheaves of sets. The canonical map from the colimit
of the sections over `W` of the finite sub-coproducts of `f` to the sections over `W` of
`∐ f` is bijective. This is Stacks 0738 part (3), applied to the filtered diagram of finite
sub-coproducts, whose transition maps are monomorphisms by `mono_liftToFinsetObj_map`. -/
theorem bijective_colimit_post_liftToFinsetObj (J : GrothendieckTopology C)
    (W : C) (hW : J.IsQuasiCompactObject W) {ι : Type max u v}
    (f : ι → Sheaf J (Type max u v)) :
    Function.Bijective (colimit.post (liftToFinsetObj (Discrete.functor f))
      ((sheafSections J (Type max u v)).obj (op W))) :=
  (CategoryTheory.Sheaf.injective_and_bijective_colimit_post_sheafSections J
      (liftToFinsetObj (Discrete.functor f)) W).2.2.1 hW
    (mono_liftToFinsetObj_map f)

/-- **Stacks 0935, the content of the proof of part (1).** Let `W` be a quasi-compact object of
a site and let `f` be a family of sheaves of sets. Sections over `W` carry the presentation of
`∐ f` as the filtered colimit of its finite sub-coproducts to a colimit of sets: the sections
over `W` of `∐_{i ∈ I} f i` are the filtered colimit, over the finite subsets `E ⊆ I`, of the
sections over `W` of `∐_{i ∈ E} f i`.

This is the whole of the source's argument for part (1). Part (1) itself, that sections over `W`
commute with coproducts, is false as stated; see the module documentation and
`not_preservesColimitsOfShape_pempty_of_bot_mem`. -/
@[stacks 0935 "part (1), the assertion the source's proof establishes: sections over a
  quasi-compact object carry the presentation of an arbitrary coproduct of sheaves of sets as the
  filtered colimit of its finite sub-coproducts to a colimit of sets. The source's part (1), that
  sections commute with coproducts, is false as stated; see the module documentation."]
noncomputable def isColimitSectionsFiniteSubcoproductsCocone (J : GrothendieckTopology C)
    (W : C) (hW : J.IsQuasiCompactObject W) {ι : Type max u v}
    (f : ι → Sheaf J (Type max u v)) :
    IsColimit (((sheafSections J (Type max u v)).obj (op W)).mapCocone
      (finiteSubcoproductsCocone f)) :=
  have _hiso : IsIso (colimit.post (liftToFinsetObj (Discrete.functor f))
      ((sheafSections J (Type max u v)).obj (op W))) :=
    (isIso_iff_bijective _).2 (bijective_colimit_post_liftToFinsetObj J W hW f)
  have : PreservesColimit (liftToFinsetObj (Discrete.functor f))
      ((sheafSections J (Type max u v)).obj (op W)) := preservesColimit_of_isIso_post _ _
  isColimitOfPreserves _ (isColimitFiniteSubproductsCocone f)

/-! ### Part (1), corrected -/

/-- **Stacks 0935, part (1), corrected.** Evaluation of sheaves of sets at a quasi-compact object
carries a filtered colimit whose transition maps are monomorphisms to a colimit of sets: the
canonical map `colim_i F_i(U) ⟶ (colim_i F_i)(U)` is bijective.

This is the approved erratum for part (1). The source's part (1) — that sections over a
quasi-compact object commute with *arbitrary* coproducts — is **false**; the counterexamples are
in this module's documentation and `not_preservesColimitsOfShape_pempty_of_bot_mem`. The corrected
statement is Stacks 0738 part (3), so this is an exact wrapper of that theorem's third conjunct
and introduces no new machinery.

`isColimitSectionsFiniteSubcoproductsCocone` below is this statement specialized to the filtered
diagram of finite sub-coproducts, whose transition maps are monomorphisms; that specialization
alone does not state the corrected part (1), which is why it is registered separately. -/
@[stacks 0935 "part (1), CORRECTED per the approved erratum: evaluation at a quasi-compact object
  carries a filtered colimit with monomorphic transition maps to a colimit of sets, which is
  Stacks 0738 part (3). The source's part (1), that sections commute with arbitrary coproducts, is
  false; the counterexamples are preserved in this module's documentation and in
  `not_preservesColimitsOfShape_pempty_of_bot_mem`."]
theorem bijective_colimit_post_sheafSections_of_isQuasiCompactObject_of_mono
    (J : GrothendieckTopology C) {I : Type w₁} [Category.{w₂} I] [IsFiltered I]
    [HasColimitsOfShape I (Type max u v)] (F : I ⥤ Sheaf J (Type max u v)) (U : C)
    (hU : J.IsQuasiCompactObject U)
    (hmono : ∀ (i j : I) (f : i ⟶ j), Mono (F.map f)) :
    Function.Bijective (colimit.post F ((sheafSections J (Type max u v)).obj (op U))) :=
  (CategoryTheory.Sheaf.injective_and_bijective_colimit_post_sheafSections J F U).2.2.1 hU hmono

/-! ### Part (1) of the source is false as stated -/

/-- A family of morphisms with fixed target and empty index type generates the empty sieve. -/
private lemma sieve₀_eq_bot {W : C} (𝒱 : PreZeroHypercover.{max u v} W) (h : IsEmpty 𝒱.I₀) :
    𝒱.sieve₀ = ⊥ := by
  ext Z g
  simp only [Sieve.bot_apply, iff_false]
  intro hg
  obtain ⟨i, _, _⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  exact h.elim i

/-- **An object covered by the empty sieve is quasi-compact** (Stacks 090H). The empty family
is a covering of such an object, and it refines every covering through the empty index map,
whose image is finite. -/
theorem isQuasiCompactObject_of_bot_mem {W : C} (hW : (⊥ : Sieve W) ∈ J W) :
    J.IsQuasiCompactObject W := by
  intro 𝒰 _
  refine ⟨{ I₀ := PEmpty.{max u v + 1}, X := fun i => i.elim, f := fun i => i.elim },
    { s₀ := fun i => i.elim, h₀ := fun i => i.elim, w₀ := fun i => i.elim }, ?_,
    Set.finite_range _⟩
  rwa [sieve₀_eq_bot _ (by infer_instance)]

/-- **Part (1) of Stacks 0935 fails at an object covered by the empty sieve.** Such an object is
quasi-compact, every sheaf has exactly one section over it, and the empty coproduct of sets is
empty; so the sections functor does not commute with the empty coproduct. -/
theorem not_preservesColimitsOfShape_pempty_of_bot_mem (J : GrothendieckTopology C) {W : C}
    (hW : (⊥ : Sieve W) ∈ J W) :
    ¬ PreservesColimitsOfShape (Discrete PEmpty.{max u v + 1})
      ((sheafSections J (Type max u v)).obj (op W)) := by
  intro h
  let D : Discrete PEmpty.{max u v + 1} ⥤ Sheaf J (Type max u v) :=
    Discrete.functor fun i => i.elim
  have hto : ((sheafSections J (Type max u v)).obj (op W)).obj (colimit D) ⟶
      PEmpty.{max u v + 1} :=
    (isColimitOfPreserves ((sheafSections J (Type max u v)).obj (op W))
      (colimit.isColimit D)).desc { pt := PEmpty.{max u v + 1}, ι := { app := fun i => i.as.elim } }
  exact (hto ((CategoryTheory.Sheaf.isTerminalOfBotCover (colimit D) W hW).from
    PUnit.{max u v + 1} PUnit.unit)).elim

/-- **Part (1) of Stacks 0935 fails in the site of opens of a topological space.** The empty
open is a quasi-compact object of `Opens X`, and the sections functor at it does not commute
with the empty coproduct of sheaves of sets. -/
theorem not_preservesColimitsOfShape_pempty_sheafSections_opens_bot (X : Type u)
    [TopologicalSpace X] :
    (Opens.grothendieckTopology X).IsQuasiCompactObject ⊥ ∧
      ¬ PreservesColimitsOfShape (Discrete PEmpty.{u + 1})
        ((sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊥)) :=
  have hbot : (⊥ : Sieve (⊥ : Opens X)) ∈ Opens.grothendieckTopology X ⊥ :=
    fun x hx => absurd hx (by simp)
  ⟨isQuasiCompactObject_of_bot_mem hbot, not_preservesColimitsOfShape_pempty_of_bot_mem _ hbot⟩

end Stacks.Sites

end

