module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkCriterion
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization of a ringed topos at a sheaf

Let `X` be a ringed topos, presented by a site `(C, J)` with a sheaf of commutative
rings `O`, and let `F` be a sheaf of sets on `C`. The localization of `X` at `F` is
the ringed topos whose site is the *site of elements* of `F` — the category
`CostructuredArrow yoneda F` of pairs `(U, s)` with `s ∈ F(U)`, equipped with the
topology restricted along the projection to `C` — and whose structure sheaf is the
restriction of `O` along that projection.

This file constructs that ringed topos and proves that the two *sectionwise*
conditions in the definition of a locally ringed topos are inherited by it. These are
the mathematical content of the topos half of Stacks Tag 04IH: the structure sheaf of
the localization is literally the restriction of `O`, so both conditions transfer by
pulling a covering sieve back along the projection.

## Main definitions

* `Stacks.Sheaves.LocalizedRingedTopos.elementSite` — the site of elements of `F`.
* `Stacks.Sheaves.LocalizedRingedTopos.elementProjection` — its projection to `C`.
* `Stacks.Sheaves.LocalizedRingedTopos.elementTopology` — the topology on the site of
  elements, as the topology restricted along the projection.
* `Stacks.Sheaves.LocalizedRingedTopos.localizedRingedTopos` — the localized ringed
  topos itself.
* `Stacks.Sheaves.LocalizedRingedTopos.liftHom` — the canonical lift of a morphism
  `g : V ⟶ Us.left` of `C` to the site of elements.

## Main results

* `Stacks.Sheaves.LocalizedRingedTopos.mem_elementTopology_of_forall_liftHom` — a sieve
  on `(U, s)` is covering for the restricted topology as soon as it contains the
  canonical lift of every arrow in some covering sieve of `U`. This is the single
  lever both transfer results below use, and it avoids computing the sieve pushforward.
* `Stacks.Sheaves.LocalizedRingedTopos.nontrivial_on_nonempty_localized` — condition
  (1) of a locally ringed topos is inherited by the localization: on an object of the
  site of elements not covered by the empty sieve, `0 ≠ 1`.
* `Stacks.Sheaves.LocalizedRingedTopos.locallyUnitOrCounit_localized` — condition (2)
  is inherited: every section of the localized structure sheaf is, on some covering,
  a unit or a co-unit.

## Implementation notes

* The ringed topos vocabulary used here is the one already in the library,
  `Stacks.Sheaves.LocallyRingedTopos.RingedTopos`, whose site objects, site morphisms and section
    rings all
  live in a single universe `u`. **Nothing is narrowed by this**: the site of elements
  `CostructuredArrow yoneda F.obj` of a sheaf on a `Type u` site with `Category.{u}`
  homs is again a `Type u` category with `Category.{u}` homs, so the localization
  stays inside `RingedTopos.{u}`. The source's statement is universe-free and the
  single-universe presentation is inherited from the library's definition, not chosen
  here.
* The topology on the site of elements is `Functor.restrictedTopology`, matching
  `StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi`, where Stacks 0791
  identifies its covering sieves with the source's coverings. The continuity and
  cocontinuity of the projection are extracted from that result rather than reproved.
* Sections of the localized structure sheaf at `(U, s)` are *definitionally* the
  sections of `O` at `U`, because the structure sheaf is the restriction
  `sheafPushforwardContinuous`, which is composition with the projection. Both
  transfer proofs rely on this: no transport along a comparison isomorphism is needed,
  and the restriction maps agree on the nose as well.
* The nested namespace `Stacks.Sheaves.LocalizedRingedTopos.OverSite` carries the same site of
  elements, projection, topology and canonical lift over a *bare* site `(C, J)` and a sheaf of
  sets on it, with independent object and morphism universes. None of that data involves the
  structure sheaf, so the bare-site form is available to a site that is not the site of a
  `RingedTopos.{u}`; `OverSite.essentiallySmall_elementSite` is stated only there, since
  essential smallness of the site of elements is likewise a property of `(C, J)` and `F` alone.
  The `RingedTopos` versions in the main namespace are what the rest of the library consumes.
* `mem_elementTopology_of_forall_liftHom` deliberately uses only the easy half of the
  characterization of the restricted topology, Mathlib's
  `Functor.mem_restrictedTopology_of_functorPushforward_mem`, together with
  `GrothendieckTopology.superset_covering`. The sieve pushforward is therefore never
  computed; it is only shown to contain the given covering sieve. In particular the
  argument needs neither local cover density of the projection nor the harder half of
  Stacks 0791.

## References

* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.LocalizedRingedTopos

universe u

/-! ### The site of elements over a bare site

The constructions below repeat the ones of the main namespace over a bare site `(C, J)` and a
sheaf of sets `F` on it, with no structure sheaf and with the object and morphism universes of
the site left independent. The site of elements, its projection, its topology and the canonical
lift of an arrow depend only on that data, so this is the form in which they apply to a site
that is not the site of a `RingedTopos.{u}`. The `RingedTopos` versions in the main namespace
are the ones the rest of the library consumes and are kept exactly as they are. -/

namespace OverSite

universe v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The site of elements of `F`: pairs `(U, s)` with `U` an object of the site
and `s` a section of `F` over `U`. -/
abbrev elementSite (F : Sheaf J (Type v)) := CostructuredArrow yoneda F.obj

/-- The projection from the site of elements of `F` to the site it lives over. -/
abbrev elementProjection (F : Sheaf J (Type v)) : elementSite F ⥤ C :=
  CostructuredArrow.proj yoneda F.obj

/-- The topology on the site of elements, restricted along the projection. By
Stacks 0791 its covering sieves are the coverings of the source. -/
abbrev elementTopology (F : Sheaf J (Type v)) : GrothendieckTopology (elementSite F) :=
  (elementProjection F).restrictedTopology J

/-- The projection from the site of elements of `F` is continuous for the restricted topology. -/
noncomputable instance elementProjection_isContinuous (F : Sheaf J (Type v)) :
    (elementProjection F).IsContinuous (elementTopology F) J := by
  obtain ⟨h, _, _, _⟩ :=
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2
  exact h

/-- The projection from the site of elements of `F` is cocontinuous for the restricted
topology. -/
noncomputable instance elementProjection_isCocontinuous (F : Sheaf J (Type v)) :
    (elementProjection F).IsCocontinuous (elementTopology F) J := by
  obtain ⟨_, h, _, _⟩ :=
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2
  exact h

/-- **The site of elements of `F` is essentially small whenever the site is.**  By the Yoneda
lemma it is the category of elements of `F`, which `CategoryTheory.Elements.essentiallySmall`
covers.  Note that Mathlib's `CostructuredArrow.essentiallySmall` does *not* apply here: it asks
for `LocallySmall.{v}` of the presheaf category, whose hom types lie in `Type (max u v)`.

This is stated over the bare site, so it serves both presentations of a ringed topos: the site of
elements depends only on the site, its topology and the sheaf, never on the structure sheaf. -/
instance essentiallySmall_elementSite [EssentiallySmall.{v} C] (F : Sheaf J (Type v)) :
    EssentiallySmall.{v} (elementSite F) :=
  (essentiallySmall_congr.{v}
    (CategoryOfElements.costructuredArrowYonedaEquivalence F.obj)).1 inferInstance

variable {F : Sheaf J (Type v)}

/-- The canonical lift of `g : V ⟶ Us.left` to a morphism of the site of elements with
target `Us`, obtained by pulling the section back along `g`. -/
abbrev liftHom (Us : elementSite F) {V : C} (g : V ⟶ Us.left) :
    CostructuredArrow.mk (yoneda.map g ≫ Us.hom) ⟶ Us :=
  CostructuredArrow.homMk g rfl

/-- A sieve on an object `Us` of the site of elements is covering for the restricted
topology as soon as it contains the canonical lift of every arrow of some covering
sieve of `Us.left`.

Only the easy half of the description of the restricted topology is used: the sieve
pushforward is shown to contain the given covering sieve, never computed. -/
theorem mem_elementTopology_of_forall_liftHom {Us : elementSite F}
    {S : Sieve Us.left} (hS : S ∈ J Us.left) {T : Sieve Us}
    (hT : ∀ ⦃V : C⦄ (g : V ⟶ Us.left), S.arrows g → T.arrows (liftHom Us g)) :
    T ∈ elementTopology F Us := by
  refine Functor.mem_restrictedTopology_of_functorPushforward_mem
    (J.superset_covering ?_ hS)
  intro V g hg
  exact ⟨_, liftHom Us g, 𝟙 V, hT g hg, by simp⟩

end OverSite

variable (X : Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u}) (F : X.Topos)

/-- The site of elements of `F`: pairs `(U, s)` with `U` an object of the site of `X`
and `s` a section of `F` over `U`. -/
abbrev elementSite := CostructuredArrow yoneda F.obj

/-- The projection from the site of elements of `F` to the site of `X`. -/
abbrev elementProjection : elementSite X F ⥤ X.C :=
  CostructuredArrow.proj yoneda F.obj

/-- The topology on the site of elements, restricted along the projection. By
Stacks 0791 its covering sieves are the coverings of the source. -/
abbrev elementTopology : GrothendieckTopology (elementSite X F) :=
  (elementProjection X F).restrictedTopology X.J

/-- The projection from the site of elements of `F` to the site of `X` is continuous for the
restricted topology. -/
noncomputable instance elementProjection_isContinuous :
    (elementProjection X F).IsContinuous (elementTopology X F) X.J := by
  obtain ⟨h, _, _, _⟩ :=
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2
  exact h

/-- The projection from the site of elements of `F` to the site of `X` is cocontinuous for the
restricted topology. -/
noncomputable instance elementProjection_isCocontinuous :
    (elementProjection X F).IsCocontinuous (elementTopology X F) X.J := by
  obtain ⟨_, h, _, _⟩ :=
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2
  exact h

/-- The **localization of the ringed topos `X` at the sheaf `F`**: the site of elements
of `F`, with the restricted topology, and with the restriction of `O` along the
projection as structure sheaf. -/
noncomputable def localizedRingedTopos : Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u} where
  C := elementSite X F
  J := elementTopology X F
  O := ((elementProjection X F).sheafPushforwardContinuous CommRingCat.{u}
    (elementTopology X F) X.J).obj X.O

variable {X F}

/-- The canonical lift of `g : V ⟶ Us.left` to a morphism of the site of elements with
target `Us`, obtained by pulling the section back along `g`. -/
abbrev liftHom (Us : elementSite X F) {V : X.C} (g : V ⟶ Us.left) :
    CostructuredArrow.mk (yoneda.map g ≫ Us.hom) ⟶ Us :=
  CostructuredArrow.homMk g rfl

/-- A sieve on an object `Us` of the site of elements is covering for the restricted
topology as soon as it contains the canonical lift of every arrow of some covering
sieve of `Us.left`.

Only the easy half of the description of the restricted topology is used: the sieve
pushforward is shown to contain the given covering sieve, never computed. -/
theorem mem_elementTopology_of_forall_liftHom {Us : elementSite X F}
    {S : Sieve Us.left} (hS : S ∈ X.J Us.left) {T : Sieve Us}
    (hT : ∀ ⦃V : X.C⦄ (g : V ⟶ Us.left), S.arrows g → T.arrows (liftHom Us g)) :
    T ∈ elementTopology X F Us :=
  OverSite.mem_elementTopology_of_forall_liftHom hS hT

/-- **Stacks Tag 04IH, condition (1) for the localization.** Localizing at a sheaf
preserves the first condition in the definition of a locally ringed topos: on an object
of the site of elements that is not covered by the empty sieve, the sections `0` and
`1` of the localized structure sheaf are distinct.

The empty sieve on `(U, s)` contains the canonical lift of every arrow of the empty
sieve on `U` vacuously, so `mem_elementTopology_of_forall_liftHom` turns a covering by
the empty sieve downstairs into one upstairs. -/
theorem nontrivial_on_nonempty_localized
    (hX : ∀ U : X.C, (⊥ : Sieve U) ∉ X.J U →
      (0 : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (op U) : CommRingCat.{u})) ≠ 1)
    (Us : (localizedRingedTopos X F).C)
    (hUs : (⊥ : Sieve Us) ∉ (localizedRingedTopos X F).J Us) :
    (0 : (((sheafToPresheaf (localizedRingedTopos X F).J CommRingCat.{u}).obj
        (localizedRingedTopos X F).O).obj (op Us) : CommRingCat.{u})) ≠ 1 := by
  intro h01
  refine hUs (mem_elementTopology_of_forall_liftHom (S := ⊥) ?_ ?_)
  · by_contra hbot
    exact hX _ hbot h01
  · intro V g hg
    exact hg.elim

/-- **Stacks Tag 04IH, condition (2) for the localization.** Localizing at a sheaf
preserves the second condition in the definition of a locally ringed topos: every
section of the localized structure sheaf is, on some covering, a unit or a co-unit.

A section over `(U, s)` is a section of `O` over `U`; pulling the covering sieve
supplied downstairs back along the projection gives the covering upstairs, and the
restriction maps agree definitionally. -/
theorem locallyUnitOrCounit_localized
    (hX : ∀ (U : X.C)
        (a : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (op U) : CommRingCat.{u})),
      Stacks.Sheaves.LocallyRingedTopos.LocallyUnitOrCounit X U a)
    (Us : (localizedRingedTopos X F).C)
    (a : (((sheafToPresheaf (localizedRingedTopos X F).J CommRingCat.{u}).obj
      (localizedRingedTopos X F).O).obj (op Us) : CommRingCat.{u})) :
    Stacks.Sheaves.LocallyRingedTopos.LocallyUnitOrCounit (localizedRingedTopos X F) Us a := by
  obtain ⟨S, hS⟩ := hX ((elementProjection X F).obj Us) a
  refine ⟨⟨Sieve.functorPullback (elementProjection X F) S.1,
    mem_elementTopology_of_forall_liftHom S.2 ?_⟩, ?_⟩
  · intro V g hg
    exact hg
  · intro W g hg
    exact hS ((elementProjection X F).map g) hg

end Stacks.Sheaves.LocalizedRingedTopos
