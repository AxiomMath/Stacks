module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Sections and stalks of an inverse image sheaf

Let `f : X ⟶ Y` be a continuous map and let `F` be a sheaf on `Y` with values in a concrete
category `C` for which the inverse image `f⁻¹ F` is defined. This file records the two things one
needs in order to compute with sections of `f⁻¹ F`:

* `Stacks.Topology.ambientSection`, the canonical map taking a section of `F` on an open `U ⊆ Y`
  to a section of `f⁻¹ F` on an open `V ⊆ f⁻¹ U`;
* `Stacks.Topology.ambientStalkHom`, the canonical map `F_{f x} ⟶ (f⁻¹ F)_x` on stalks, which is
  an isomorphism, together with `Stacks.Topology.germ_ambientSection`, which says that it carries
  the germ of a section of `F` at `f x` to the germ at `x` of the induced section of `f⁻¹ F`.

Together these say that a section of `f⁻¹ F` is, germ by germ, a section of `F`: the content of
[Stacks, Tag 008H] in the form in which the sections of an inverse image are actually computed.

## Main definitions

* `Stacks.Topology.ambientSection`: the canonical map `F(U) ⟶ (f⁻¹F)(V)` for `V ≤ f⁻¹ U`.
* `Stacks.Topology.ambientStalkHom`: the canonical map `F_{f x} ⟶ (f⁻¹F)_x`.

## Main results

* `Stacks.Topology.isIso_ambientStalkHom`: the stalk comparison is an isomorphism.
* `Stacks.Topology.germ_ambientSection`: the stalk comparison takes germs to germs.
* `Stacks.Topology.ambientSection_map`: restricting a section of `F` to a smaller open of `Y`
  does not change the induced section of `f⁻¹ F`.
* `Stacks.Topology.exists_ambientSection_germ`: every element of a stalk of `f⁻¹ F` is the image
  of the germ of a section of `F` on an open neighbourhood of the image point.
* `Stacks.Topology.unit_comp_map_pullbackIso_hom`: the comparison of the two models of the sheaf
  inverse image carries the unit of the abstract adjunction to the unit of the constructed one,
  at arbitrary coefficients. This is the first step of identifying `ambientSection` with that
  unit; `Stacks.Topology.pullbackIso_unit` has it for sheaves of sets only. The identification
  itself is completed in `Topology/Sheaves/Functors/Pullback/UnitOnSections.lean`
  (`Stacks.Topology.ambientSection_eq_unit`).

## Implementation notes

Everything is stated for an arbitrary coefficient category carrying the typeclasses under which
`TopCat.Sheaf.pullback` is defined — in particular for `Type u` and for `AddCommGrpCat.{u}`. The
previously recorded obstruction that the comparison is available only for sheaves of sets is not
real: Mathlib's `TopCat.Presheaf.stalkPullbackIso` and
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, out of which the comparison is built,
are stated at that same generality.

`ambientSection` goes through the *presheaf* inverse image and then sheafifies, rather than
through the unit of the sheaf-level adjunction, because that is the route along which the germ
computation is available: `TopCat.Presheaf.germ_stalkPullbackHom` identifies the presheaf unit
with the stalk comparison, and sheafification is then transparent on stalks.

Neither the germ compatibility nor the naturality is proved by rewriting. In these goals the two
spellings `P.stalk x` and `(stalkFunctor C x).obj P` of one object are definitionally but not
syntactically equal, so `rw` and `simp` reject the rewrite as not type-correct at the `implicit`
transparency level; the identities are therefore applied as terms, with `congrArg` and `Eq.trans`.

## References

* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The inverse image of the underlying presheaf of a sheaf, before sheafification. -/
abbrev inverseImagePresheaf (F : Y.Sheaf C) : X.Presheaf C :=
  (Presheaf.pullback C f).obj F.presheaf

/-- The underlying presheaf of the inverse image sheaf is the sheafification of the inverse image
presheaf. This is `TopCat.Sheaf.pullbackIso` with the sheaf condition forgotten. -/
def sheafPullbackPresheafIso (F : Y.Sheaf C) :
    ((TopCat.Sheaf.pullback C f).obj F).presheaf ≅
      CategoryTheory.sheafify (Opens.grothendieckTopology X) (inverseImagePresheaf f F) :=
  (TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app F)

/-- **The stalk comparison for an inverse image sheaf**: the canonical map from the stalk of `F`
at `f x` to the stalk of `f⁻¹ F` at `x`. It is the presheaf-level comparison
`TopCat.Presheaf.stalkPullbackHom` followed by the identification of the stalks of a presheaf and
of its sheafification. -/
def ambientStalkHom (F : Y.Sheaf C) (x : X) :
    F.presheaf.stalk (f x) ⟶ ((TopCat.Sheaf.pullback C f).obj F).presheaf.stalk x :=
  Presheaf.stalkPullbackHom C f F.presheaf x ≫
    (Presheaf.stalkFunctor C x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (inverseImagePresheaf f F)) ≫
    (Presheaf.stalkFunctor C x).map (sheafPullbackPresheafIso f F).inv

/-- **The stalk of an inverse image sheaf is the stalk of the sheaf at the image point**
([Stacks, Tag 008H]). -/
instance isIso_ambientStalkHom (F : Y.Sheaf C) (x : X) : IsIso (ambientStalkHom f F x) := by
  have h₁ : IsIso (Presheaf.stalkPullbackHom C f F.presheaf x) :=
    (Presheaf.stalkPullbackIso C f F.presheaf x).isIso_hom
  have h₂ : IsIso ((Presheaf.stalkFunctor C x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (inverseImagePresheaf f F))) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x C _
  have h₃ : IsIso ((Presheaf.stalkFunctor C x).map (sheafPullbackPresheafIso f F).inv) :=
    inferInstance
  dsimp only [ambientStalkHom]
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)

/-- The canonical map taking a section of `F` on an open `U` of `Y` to a section of the inverse
image sheaf `f⁻¹ F` on an open `V` of `X` contained in `f⁻¹ U`. -/
def ambientSection (F : Y.Sheaf C) {U : Opens Y} {V : Opens X}
    (h : V ≤ (Opens.map f).obj U) :
    F.presheaf.obj (op U) ⟶ ((TopCat.Sheaf.pullback C f).obj F).presheaf.obj (op V) :=
  ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
    (inverseImagePresheaf f F).map (homOfLE h).op ≫
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f F)).app (op V) ≫
    (sheafPullbackPresheafIso f F).inv.app (op V)

/-- **The stalk comparison takes germs to germs.** The germ at `x` of the section of `f⁻¹ F`
induced by a section `s` of `F` is the image of the germ of `s` at `f x`. -/
theorem germ_ambientSection (F : Y.Sheaf C) {U : Opens Y} {V : Opens X}
    (h : V ≤ (Opens.map f).obj U) (x : X) (hx : x ∈ V)
    (s : ToType (F.presheaf.obj (op U))) :
    ((TopCat.Sheaf.pullback C f).obj F).presheaf.germ V x hx (ambientSection f F h s) =
      ambientStalkHom f F x (F.presheaf.germ U (f x) (h hx) s) := by
  simp only [ambientSection, ambientStalkHom]
  simp only [ConcreteCategory.comp_apply]
  rw [← Presheaf.stalkFunctor_map_germ_apply, ← Presheaf.stalkFunctor_map_germ_apply,
    Presheaf.germ_res_apply]
  have key := ConcreteCategory.congr_hom
    (Presheaf.germ_stalkPullbackHom C f F.presheaf x U (h hx)) s
  simp only [ConcreteCategory.comp_apply] at key
  exact (congrArg _ (congrArg _ key.symm)).trans (ConcreteCategory.comp_apply _ _ _).symm

/-- Restricting a section of `F` to a smaller open of `Y` does not change the section it induces
on an open of `X` lying inside both inverse images. -/
theorem ambientSection_map_apply (F : Y.Sheaf C) {U U' : Opens Y} {V : Opens X} (m : U' ⟶ U)
    (h : V ≤ (Opens.map f).obj U') (h' : V ≤ (Opens.map f).obj U)
    (s : ToType (F.presheaf.obj (op U))) :
    ambientSection f F h (F.presheaf.map m.op s) = ambientSection f F h' s := by
  have hnat := ConcreteCategory.congr_hom
    (((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).naturality m.op) s
  simp only [Functor.id_obj, ConcreteCategory.comp_apply] at hnat
  have hres : ((Presheaf.pullback C f ⋙ Presheaf.pushforward C f).obj F.presheaf).map m.op ≫
      (inverseImagePresheaf f F).map (homOfLE h).op =
      (inverseImagePresheaf f F).map (homOfLE h').op := by
    change (inverseImagePresheaf f F).map ((Opens.map f).op.map m.op) ≫ _ = _
    rw [← Functor.map_comp]
    exact congrArg _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have hcomp : ∀ w, (inverseImagePresheaf f F).map (homOfLE h).op
        (((Presheaf.pullback C f ⋙ Presheaf.pushforward C f).obj F.presheaf).map m.op w) =
      (inverseImagePresheaf f F).map (homOfLE h').op w := fun w ↦
    (ConcreteCategory.comp_apply _ _ w).symm.trans (ConcreteCategory.congr_hom hres w)
  simp only [ambientSection, ConcreteCategory.comp_apply]
  exact congrArg _ (congrArg _ ((congrArg _ hnat).trans (hcomp _)))

/-- Restricting a section of `F` to a smaller open of `Y` does not change the section it induces
on an open of `X` lying inside both inverse images, as an identity of morphisms. -/
theorem ambientSection_map (F : Y.Sheaf C) {U U' : Opens Y} {V : Opens X} (m : U' ⟶ U)
    (h : V ≤ (Opens.map f).obj U') (h' : V ≤ (Opens.map f).obj U) :
    F.presheaf.map m.op ≫ ambientSection f F h = ambientSection f F h' :=
  ConcreteCategory.hom_ext _ _ fun s ↦
    (ConcreteCategory.comp_apply _ _ s).trans (ambientSection_map_apply f F m h h' s)

/-- **Every element of a stalk of an inverse image sheaf comes from a section of the sheaf.**
For `t` in the stalk of `f⁻¹ F` at `x` there is a section of `F` on an open neighbourhood of
`f x` whose germ the stalk comparison carries to `t`. -/
theorem exists_ambientSection_germ (F : Y.Sheaf C) (x : X)
    (t : ToType (((TopCat.Sheaf.pullback C f).obj F).presheaf.stalk x)) :
    ∃ (U : Opens Y) (hU : f x ∈ U) (s : ToType (F.presheaf.obj (op U))),
      ambientStalkHom f F x (F.presheaf.germ U (f x) hU s) = t := by
  obtain ⟨t', rfl⟩ := (ConcreteCategory.bijective_of_isIso (ambientStalkHom f F x)).2 t
  obtain ⟨U, hU, s, rfl⟩ := F.presheaf.exists_germ_eq t'
  exact ⟨U, hU, s, rfl⟩

/-- **The comparison of the two models of the sheaf inverse image carries the unit of the
abstract adjunction to the unit of the constructed one**, at arbitrary coefficients.

`Stacks.Topology.pullbackIso_unit` is this statement for sheaves of *sets* only; this is it at
the coefficient generality `ambientSection` is stated at, in particular for abelian sheaves. It
is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, the two left adjoints being the
abstract `TopCat.Sheaf.pullback` and the sheafification of the presheaf inverse image: their
comparison `TopCat.Sheaf.pullbackIso` *is* `Adjunction.leftAdjointUniq` of the two adjunctions
by construction.

It is the first step of the identification of `ambientSection f F (le_refl _)` with
`((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op U)`. What remains
after it is the identification of the unit of the *constructed* adjunction with the presheaf
unit followed by `toSheafify`, which `Stacks.Topology.pullbackConstruction_unit` supplies for
sheaves of sets by `rfl` and which is not `rfl` at general coefficients, composition of
morphisms there not being composition of functions. That step is
`Stacks.Topology.sheafPullbackConstruction_unit_map` of
`Topology/Sheaves/Functors/Pullback/UnitOnSections.lean`, proved there over an arbitrary site,
and the identification is completed in that file as
`Stacks.Topology.ambientSection_eq_unit`. -/
theorem unit_comp_map_pullbackIso_hom (F : Y.Sheaf C) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F ≫
        (TopCat.Sheaf.pushforward C f).map ((TopCat.Sheaf.pullbackIso C f).hom.app F) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) C
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app F :=
  CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The stalk comparison is injective on elements, being an isomorphism. -/
theorem ambientStalkHom_injective (F : Y.Sheaf C) (x : X) :
    Function.Injective (ambientStalkHom f F x) :=
  (ConcreteCategory.bijective_of_isIso (ambientStalkHom f F x)).1

end

end Stacks.Topology

end
