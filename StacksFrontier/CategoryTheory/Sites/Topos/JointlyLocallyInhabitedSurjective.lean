module

public import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Topos.JointlyLocallyInhabited
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Joint local inhabitedness and surjectivity onto the final sheaf

For a family `G : I → Sheaf J (Type w)` of sheaves of types on a site and a family of morphisms
`c i : G i ⟶ Y` into a **terminal** sheaf, the two ways of saying that the family jointly covers
the site agree:

* `∐ᵢ Gᵢ ⟶ Y` is a surjection of sheaves, i.e. `CategoryTheory.Sheaf.IsLocallySurjective` of
  `CategoryTheory.Limits.Sigma.desc c`;
* every object of the site is covered by objects over which some `G i` has a section, i.e.
  `Stacks.Topos.JointlyLocallyInhabited J G`.

This file proves the equivalence, `Stacks.Topos.isLocallySurjective_sigmaDesc_iff_of_isTerminal`.
Both directions are short, and the point of recording them is that the two conditions have
*different hypotheses*: the coproduct form needs `HasCoproduct G`, which for `Type w`-valued
sheaves constrains the index universe, while the sieve form needs nothing at all.  So a
consumer whose index type is too large for a coproduct to exist can still be served by the
sieve form, and `Stacks.Topos.jointlyLocallyInhabited_inverseImage` transports the sieve form
along a morphism of topoi with no colimit anywhere in sight.

The file also records that a family of *representable* sheaves on a subcanonical site is
jointly locally inhabited exactly when the representing objects cover the final object
(`Stacks.Topos.jointlyLocallyInhabited_yoneda_iff_coversTop`): the sieve
`Stacks.Topos.inhabitedSieve` of the representables is `CategoryTheory.Sieve.ofObjects` of the
objects, on the nose.

## Main results

* `Stacks.Topos.subsingleton_sections_of_isTerminal` and
  `Stacks.Topos.nonempty_sections_of_isTerminal` — a terminal sheaf of types has exactly one
  section over every object.
* `Stacks.Topos.jointlyLocallyInhabited_yoneda_iff_coversTop` — on a subcanonical site, a family
  of representable sheaves is jointly locally inhabited exactly when the representing objects
  cover the final object.
* `Stacks.Topos.isLocallySurjective_sigmaDesc_of_jointlyLocallyInhabited` — joint local
  inhabitedness makes `∐ᵢ Gᵢ ⟶ Y` a surjection of sheaves, for any family of morphisms into a
  terminal sheaf.
* `Stacks.Topos.jointlyLocallyInhabited_of_isLocallySurjective_sigmaDesc` — the converse.
* `Stacks.Topos.isLocallySurjective_sigmaDesc_iff_of_isTerminal` — the two together.

## Implementation notes

The target is an arbitrary sheaf with a terminal-object witness rather than `⊤_ (Sheaf J A)` or
the constant sheaf `PUnit`, because a consumer that has produced a surjection onto one
presentation of the final sheaf has produced it onto every other: the only thing either
direction uses is that the sections of the target over an object form a singleton.

`CategoryTheory.Sheaf.isLocallySurjective_terminal_from_sigma_sheafifiedYoneda` of
`StacksFrontier/CategoryTheory/Sites/QuasiCompact/CoveringSetFromCoversTop.lean` is the forward
direction for the *sheafified* representables of a site, and is the special case
`c i = terminal.from (G i)`, `G i = h_{U i}^#` of the statement here.  It does not apply at the
universes of interest to the small étale site of an algebraic space: it is stated for sheaves of
`Type (max u v)`, whereas that site has objects in `Type (u + 1)` and sheaves of `Type u`.  This
file is therefore stated at an unconstrained section universe `w` and an unconstrained index
universe.

## References

* [Stacks Project, Tag 00WI](https://stacks.math.columbia.edu/tag/00WI)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace Stacks.Topos

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {I : Type w'}

/-! ### Sections of a terminal sheaf of types -/

/-- **A terminal sheaf of types has at most one section over every object.**  Evaluation at an
object is the composite of `CategoryTheory.sheafToPresheaf` with an evaluation functor, both of
which preserve the terminal object, so the sections are a terminal type. -/
theorem subsingleton_sections_of_isTerminal {Y : Sheaf J (Type w)} (hY : IsTerminal Y)
    (U : Cᵒᵖ) : Subsingleton (Y.obj.obj U) := by
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U
  let _ : Unique (Y.obj.obj U) := Types.isTerminalEquivUnique _ (hY.isTerminalObj E)
  infer_instance

/-- **A terminal sheaf of types has a section over every object.**  See
`Stacks.Topos.subsingleton_sections_of_isTerminal` for the uniqueness. -/
theorem nonempty_sections_of_isTerminal {Y : Sheaf J (Type w)} (hY : IsTerminal Y)
    (U : Cᵒᵖ) : Nonempty (Y.obj.obj U) := by
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U
  let _ : Unique (Y.obj.obj U) := Types.isTerminalEquivUnique _ (hY.isTerminalObj E)
  infer_instance

/-! ### Representable sheaves on a subcanonical site -/

/-- **On a subcanonical site, a family of representable sheaves is jointly locally inhabited
exactly when the representing objects cover the final object.**  A section of `h_{Y i}` over an
object is a morphism into `Y i`, so `Stacks.Topos.inhabitedSieve` of the representables is
`CategoryTheory.Sieve.ofObjects` of the objects and the two conditions are the same sieves
being covering. -/
theorem jointlyLocallyInhabited_yoneda_iff_coversTop [J.Subcanonical] (Y : I → C) :
    JointlyLocallyInhabited J (fun i => J.yoneda.obj (Y i)) ↔ J.CoversTop Y :=
  Iff.rfl

/-- The representable sheaves of a family of objects covering the final object of a subcanonical
site are jointly locally inhabited.  This is the direction of
`Stacks.Topos.jointlyLocallyInhabited_yoneda_iff_coversTop` that a consumer uses. -/
theorem jointlyLocallyInhabited_yoneda_of_coversTop [J.Subcanonical] {Y : I → C}
    (hY : J.CoversTop Y) : JointlyLocallyInhabited J (fun i => J.yoneda.obj (Y i)) :=
  hY

/-! ### Surjectivity onto the final sheaf -/

/-- **A jointly locally inhabited family surjects onto the final sheaf.**  If every object of the
site is covered by objects carrying a section of some `G i`, then for any family of morphisms
`c i : G i ⟶ Y` into a terminal sheaf the induced morphism `∐ᵢ Gᵢ ⟶ Y` is a surjection of
sheaves.

Over an object of the covering, a section of some `G i` gives a section of the coproduct through
the coprojection, and being a preimage of the prescribed section of `Y` is automatic because the
sections of a terminal sheaf over an object form a singleton. -/
theorem isLocallySurjective_sigmaDesc_of_jointlyLocallyInhabited {G : I → Sheaf J (Type w)}
    [HasCoproduct G] {Y : Sheaf J (Type w)} (hY : IsTerminal Y) (c : ∀ i, G i ⟶ Y)
    (hG : JointlyLocallyInhabited J G) :
    Sheaf.IsLocallySurjective (Sigma.desc c) := by
  constructor
  intro U s
  refine J.superset_covering ?_ (hG U)
  rintro V g ⟨i, ⟨x⟩⟩
  exact ⟨(Sigma.ι G i).hom.app (op V) x,
    (subsingleton_sections_of_isTerminal J hY (op V)).elim _ _⟩

/-- **A family surjecting onto the final sheaf is jointly locally inhabited.**  This is the
converse of `Stacks.Topos.isLocallySurjective_sigmaDesc_of_jointlyLocallyInhabited`.

A terminal sheaf has a section over the given object, and
`CategoryTheory.Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc` turns the surjectivity into
a covering sieve each of whose arrows has that section in the image of a single `c i`; in
particular the source of each such arrow carries a section of some `G i`. -/
theorem jointlyLocallyInhabited_of_isLocallySurjective_sigmaDesc {G : I → Sheaf J (Type w)}
    [HasCoproduct G] {Y : Sheaf J (Type w)} (hY : IsTerminal Y) (c : ∀ i, G i ⟶ Y)
    (hc : Sheaf.IsLocallySurjective (Sigma.desc c)) :
    JointlyLocallyInhabited J G := by
  intro U
  obtain ⟨T, hT, hTsec⟩ := Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc c hc
    (nonempty_sections_of_isTerminal J hY (op U)).some
  refine J.superset_covering (fun {V} g hg => ?_) hT
  obtain ⟨i, t, -⟩ := hTsec g hg
  exact ⟨i, ⟨t⟩⟩

/-- **Surjecting onto the final sheaf and being jointly locally inhabited are the same
condition.**  The two directions are
`Stacks.Topos.isLocallySurjective_sigmaDesc_of_jointlyLocallyInhabited` and
`Stacks.Topos.jointlyLocallyInhabited_of_isLocallySurjective_sigmaDesc`.

The right-hand side does not mention `Y`, `c` or the coproduct, which is the content: the
surjectivity is independent of which presentation of the final sheaf and which family of
morphisms into it the caller chose. -/
theorem isLocallySurjective_sigmaDesc_iff_of_isTerminal {G : I → Sheaf J (Type w)}
    [HasCoproduct G] {Y : Sheaf J (Type w)} (hY : IsTerminal Y) (c : ∀ i, G i ⟶ Y) :
    Sheaf.IsLocallySurjective (Sigma.desc c) ↔ JointlyLocallyInhabited J G :=
  ⟨jointlyLocallyInhabited_of_isLocallySurjective_sigmaDesc J hY c,
    isLocallySurjective_sigmaDesc_of_jointlyLocallyInhabited J hY c⟩

end Stacks.Topos

end
