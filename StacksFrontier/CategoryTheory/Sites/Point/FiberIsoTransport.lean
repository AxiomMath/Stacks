module

public import Mathlib.CategoryTheory.Limits.Final
public import StacksFrontier.CategoryTheory.Sites.Point.Exactness

/-!
# Transporting a point of a site along an isomorphism of its fibre functor

A point of a site (`CategoryTheory.GrothendieckTopology.Point`) carries exactly one piece of
data, its fibre functor `C ⥤ Type w`; the remaining fields are propositions. So two points with
*equal* fibres are equal, which is what
`CategoryTheory.GrothendieckTopology.Point.sheafFiberIsoOfFiberEq` exploits to identify the
stalk of an inverse image with the stalk at the image point.

In geometry the fibre comparison one actually has is an **isomorphism**, not an equality: for
chart base change along a morphism of algebraic spaces the lifts of a geometric point into
`V ×_X Z` and the lifts of its image into `V` are different subtypes, canonically bijective but
not definitionally equal. This file supplies the missing step — a point transports along an
isomorphism of its fibre, and its fibre functors on presheaves and on sheaves transport with
it — and then packages the two together into the form the geometry consumes.

## Main definitions

* `Stacks.SitePointFiberIso.elementsEquivOfIso`: an isomorphism of functors `C ⥤ Type w`
  induces an equivalence of their categories of elements, commuting with the projections to `C`
  on the nose.
* `Stacks.SitePointFiberIso.pointOfFiberIso`: a point of a site whose fibre is isomorphic to a
  given functor `G` yields a point with fibre `G`.
* `Stacks.SitePointFiberIso.presheafFiberIsoOfFiberIso` and `sheafFiberIsoOfFiberIso`: the
  fibre functors of the two points on presheaves, and on sheaves, are isomorphic.

## Main results

* `Stacks.SitePointFiberIso.skyscraperSheafFunctor_eq_of_fiber_eq`: the restatement of
  `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafFunctor_eq_of_fiber_eq` for sites
  whose objects and morphisms lie in **different** universes, with coefficients in the universe
  of the morphisms.
* `Stacks.SitePointFiberIso.sheafFiberIsoOfAdj`: the same restatement of
  `Point.sheafFiberIsoOfFiberEq`, with the inverse image supplied as an arbitrary left adjoint
  rather than through `CategoryTheory.Functor.sheafPullback`.
* `Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj`: **the form the geometry consumes.**
  For a continuous `uf : C ⥤ D`, a point `Phi` of `(D, K)`, a point `Psi` of `(C, J)` whose
  fibre is merely *isomorphic* to `uf ⋙ Phi.fiber`, and any left adjoint `L` of the direct
  image, the fibre functor of `Psi` on sheaves is `L` followed by that of `Phi`.

## Why the universes matter

`Point.sheafFiberIsoOfFiberEq` is stated for `C D : Type u` with `Category.{u}` — small
categories — and coefficients `Type u`. The small étale site of an algebraic space over a scheme
of universe `u` has objects in `Type (u + 1)` and morphisms in `Type u`, and the sheaves of sets
that its sheaves of modules are built from take values in `Type u`. The restatements below are
therefore at `C D : Type (u + 1)` with `Category.{u}` and coefficients `Type u`; the proofs are
the original ones, which never used smallness.

This is what makes the argument of [Stacks, Tag 04CA] available at the universe the modules live
at. **No `ULift` is needed**: it is only the identification of a point's fibre with the
*bespoke* set-valued stalk `AlgebraicGeometry.Space.stalkSet` — an un-shrunk colimit quotient,
which lands one universe up — that forces a lift. Working natively with `Point.sheafFiber`, as
here, avoids the mismatch entirely, and conservativity of a family of points is already stated
in exactly those terms, as the field
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms_type`.

Two remarks on notes elsewhere in the library.

* The implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleToposRingUniverse.lean` state that the
  spaces-étale site "is not known to be essentially small" and that consequently the inverse
  image at `Type u` is not known to be left exact, so that there is no morphism of topoi at that
  universe. That is **not the case**: `AlgebraicGeometry.Space.essentiallySmall_spacesEtale`
  is proved, and `AlgebraicGeometry.Space.smallToposMorphismTypeU` is a genuine
  `MorphismOfTopoi` at `Type u`, carrying an adjunction.
* Consequently the abelian chain of
  `StacksFrontier/AlgebraicGeometry/Spaces/ComplexesWithSupport.lean` does **not** have to be
  re-derived at `Type u` in order to reach the modules, and no `HasSheafify` instance for
  `AddCommGrpCat.{u}` on the spaces-étale site is required: the set-valued route through
  `Point.sheafFiber` reaches the module universe directly.

## Implementation notes

`CategoryOfElements.map e.hom` is shown to be an equivalence by full faithfulness and essential
surjectivity rather than by exhibiting an inverse: Mathlib has no `map_id`/`map_comp` for
`CategoryOfElements.map`, so the unit and counit of a hand-built equivalence would have to be
assembled from `eqToIso`, whereas fullness and faithfulness are immediate from the projection to
`C` being faithful and from `e` being pointwise bijective. The three are plain `theorem`s, not
instances, and `CategoryTheory.Functor.IsEquivalence` — being a `Prop` — is assembled from them
inside the definition, so that **this file adds no global instance at all**.

The projections commute on the nose — `CategoryOfElements.map_π` is `rfl` — which is what lets
the colimit comparison be Mathlib's `CategoryTheory.Functor.Final.colimIso` applied to the
opposite of the equivalence, with no transport of diagrams.

`CategoryTheory.Limits.HasColimitsOfShape` is **data**, so the colimit comparison is sensitive to
*which* instance term is in scope: introducing a fresh one with `haveI` makes the two
`presheafFiber`s non-definitionally-equal and the comparison fails to typecheck. The instance for
the transported point's category of elements is therefore produced by `letI` from
`inferInstanceAs`, which is both the canonical term and zeta-transparent.

## References

* [Stacks Project, Tag 0F4G](https://stacks.math.columbia.edu/tag/0F4G)
* [Stacks Project, Tag 00YK](https://stacks.math.columbia.edu/tag/00YK)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

namespace Stacks.SitePointFiberIso

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology

universe w v u v' u'

/-! ### The category of elements transports along an isomorphism -/

section Elements

variable {C : Type u} [Category.{v} C] {F1 F2 : C ⥤ Type w}

/-- A component of an isomorphism of `Type w`-valued functors is bijective on elements. -/
theorem bijective_app (e : F1 ≅ F2) (X : C) :
    Function.Bijective (ConcreteCategory.hom (e.hom.app X)) :=
  (ConcreteCategory.isIso_iff_bijective (e.app X).hom).1 inferInstance

/-- Applying a component of an isomorphism to the element is injective. -/
theorem injective_app (e : F1 ≅ F2) (X : C) :
    Function.Injective (ConcreteCategory.hom (e.hom.app X)) := (bijective_app e X).1

/-- Transporting an element back and forth along an isomorphism returns it. -/
theorem hom_inv_app_apply (e : F1 ≅ F2) (X : C) (y : F2.obj X) :
    e.hom.app X (e.inv.app X y) = y := by
  simp

/-- The functor on categories of elements induced by an isomorphism is faithful. -/
theorem faithful_elementsMap (e : F1 ≅ F2) :
    (CategoryOfElements.map e.hom).Faithful where
  map_injective {t1 t2} _k1 _k2 h :=
    Subtype.ext (congrArg
      (fun m : (CategoryOfElements.map e.hom).obj t1 ⟶
        (CategoryOfElements.map e.hom).obj t2 => m.val) h)

/-- The functor on categories of elements induced by an isomorphism is full. -/
theorem full_elementsMap (e : F1 ≅ F2) : (CategoryOfElements.map e.hom).Full where
  map_surjective {t1 t2} g := by
    refine ⟨⟨g.val, ?_⟩, Subtype.ext rfl⟩
    refine injective_app e t2.1 ?_
    have hnat := ConcreteCategory.congr_hom (e.hom.naturality g.val) t1.2
    simp only [types_comp_apply] at hnat
    exact hnat.trans g.property

/-- The functor on categories of elements induced by an isomorphism is essentially
surjective. -/
theorem essSurj_elementsMap (e : F1 ≅ F2) :
    (CategoryOfElements.map e.hom).EssSurj where
  mem_essImage s := by
    refine ⟨⟨s.1, e.inv.app s.1 s.2⟩, ⟨eqToIso ?_⟩⟩
    exact congrArg (fun y => (⟨s.1, y⟩ : F2.Elements)) (hom_inv_app_apply e s.1 s.2)

/-- An isomorphism of `Type w`-valued functors induces an equivalence of their categories of
elements, given on objects by transporting the element along the isomorphism. -/
def elementsEquivOfIso (e : F1 ≅ F2) : F1.Elements ≌ F2.Elements :=
  haveI : (CategoryOfElements.map e.hom).IsEquivalence :=
    { faithful := faithful_elementsMap e
      full := full_elementsMap e
      essSurj := essSurj_elementsMap e }
  (CategoryOfElements.map e.hom).asEquivalence

/-- The equivalence of categories of elements commutes with the projections to `C` on the
nose. -/
theorem elementsEquivOfIso_functor_comp_pi (e : F1 ≅ F2) :
    (elementsEquivOfIso e).functor ⋙ CategoryOfElements.π F2 = CategoryOfElements.π F1 := rfl

end Elements

/-! ### Transporting a point along an isomorphism of its fibre -/

section Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A point of a site whose fibre functor is isomorphic to `G` gives a point with fibre `G`.

The three remaining fields of `CategoryTheory.GrothendieckTopology.Point` are propositions:
cofilteredness and initial smallness of the category of elements transport along
`Stacks.SitePointFiberIso.elementsEquivOfIso`, and joint surjectivity transports by chasing an
element through the isomorphism. -/
def pointOfFiberIso (Psi : Point.{w} J) {G : C ⥤ Type w} (e : Psi.fiber ≅ G) :
    Point.{w} J where
  fiber := G
  isCofiltered := IsCofiltered.of_equivalence (elementsEquivOfIso e)
  initiallySmall :=
    initiallySmall_of_initial_of_initiallySmall (elementsEquivOfIso e).functor
  jointly_surjective {Y} R hR x := by
    obtain ⟨W, f, hf, y, hy⟩ := Psi.jointly_surjective R hR (e.inv.app Y x)
    refine ⟨W, f, hf, e.hom.app W y, ?_⟩
    have hnat := ConcreteCategory.congr_hom (e.hom.naturality f) y
    simp only [types_comp_apply] at hnat
    rw [← hnat, hy]
    exact hom_inv_app_apply e Y x

/-- The fibre functor of `pointOfFiberIso Psi e` is `G`. -/
@[simp]
theorem pointOfFiberIso_fiber (Psi : Point.{w} J) {G : C ⥤ Type w} (e : Psi.fiber ≅ G) :
    (pointOfFiberIso Psi e).fiber = G := rfl

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- The fibre functors on presheaves of two points with isomorphic fibres are isomorphic: the
projections from the two categories of elements agree through the induced equivalence, so the
two colimits are the same colimit reindexed along an equivalence. -/
def presheafFiberIsoOfFiberIso (Psi : Point.{w} J) {G : C ⥤ Type w} (e : Psi.fiber ≅ G) :
    Psi.presheafFiber (A := A) ≅ (pointOfFiberIso Psi e).presheafFiber (A := A) :=
  letI : HasColimitsOfShape (G.Elements)ᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape ((pointOfFiberIso Psi e).fiber.Elements)ᵒᵖ A)
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft (G.Elements)ᵒᵖ Cᵒᵖ A).obj (CategoryOfElements.π G).op)
    (Functor.Final.colimIso (elementsEquivOfIso e).functor.op)

/-- The fibre functors on sheaves of two points with isomorphic fibres are isomorphic: the fibre
functor on sheaves is the one on presheaves precomposed with the inclusion of sheaves. -/
def sheafFiberIsoOfFiberIso (Psi : Point.{w} J) {G : C ⥤ Type w} (e : Psi.fiber ≅ G) :
    Psi.sheafFiber (A := A) ≅ (pointOfFiberIso Psi e).sheafFiber (A := A) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafFiberIsoOfFiberIso Psi e)

end Point

/-! ### The identification of the fibre of an inverse image, at unequal site universes -/

section Transport

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}

/-- **`CategoryTheory.GrothendieckTopology.Point.skyscraperSheafFunctor_eq_of_fiber_eq` for a
site whose objects and morphisms lie in different universes.** The skyscraper sheaf functor of a
point `Psi` of `(C, J)` whose fibre is `uf ⋙ Phi.fiber` agrees on the nose with the composite of
the skyscraper of `Phi` with the direct image along `uf`.

The original is stated for small sites; the proof never uses smallness. -/
theorem skyscraperSheafFunctor_eq_of_fiber_eq (Phi : Point.{u} K) (uf : C ⥤ D)
    [uf.IsContinuous J K] (Psi : Point.{u} J) (h : Psi.fiber = uf ⋙ Phi.fiber) :
    Phi.skyscraperSheafFunctor (A := Type u) ⋙ uf.sheafPushforwardContinuous (Type u) J K =
      Psi.skyscraperSheafFunctor := by
  obtain ⟨f, _, _, _⟩ := Psi
  simp only [] at h
  subst h
  rfl

/-- **`CategoryTheory.GrothendieckTopology.Point.sheafFiberIsoOfFiberEq` at unequal site
universes, and for an arbitrary left adjoint.** If `uf : C ⥤ D` is continuous, `L` is left
adjoint to the direct image along `uf`, and `Psi` is a point of `(C, J)` whose fibre is
`uf ⋙ Phi.fiber`, then the fibre functor of `Psi` on sheaves is `L` followed by that of `Phi`.

Taking the inverse image as an arbitrary left adjoint rather than as
`CategoryTheory.Functor.sheafPullback` avoids assuming that the direct image is a right adjoint
as an instance, which on a site whose objects lie above its coefficients is a theorem rather
than an instance. -/
def sheafFiberIsoOfAdj (Phi : Point.{u} K) (uf : C ⥤ D) [uf.IsContinuous J K]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (adj : L ⊣ uf.sheafPushforwardContinuous (Type u) J K)
    (Psi : Point.{u} J) (h : Psi.fiber = uf ⋙ Phi.fiber) :
    Psi.sheafFiber (A := Type u) ≅ L ⋙ Phi.sheafFiber :=
  (conjugateIsoEquiv (adj.comp Phi.skyscraperSheafAdjunction)
      Psi.skyscraperSheafAdjunction).symm
    (eqToIso (skyscraperSheafFunctor_eq_of_fiber_eq Phi uf Psi h))

/-- **The form the geometry consumes.** If `uf : C ⥤ D` is continuous, `L` is left adjoint to
the direct image along `uf`, and the fibre of a point `Psi` of `(C, J)` is merely *isomorphic*
to `uf ⋙ Phi.fiber`, then the fibre functor of `Psi` on sheaves is still `L` followed by that
of `Phi`.

This is `Stacks.SitePointFiberIso.sheafFiberIsoOfAdj` at the transported point
`Stacks.SitePointFiberIso.pointOfFiberIso`, composed with
`Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIso`. An isomorphism is what the geometric fibre
comparison of a base-change square supplies; an equality is not. -/
def sheafFiberIsoOfFiberIsoOfAdj (Phi : Point.{u} K) (uf : C ⥤ D) [uf.IsContinuous J K]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (adj : L ⊣ uf.sheafPushforwardContinuous (Type u) J K)
    (Psi : Point.{u} J) (e : Psi.fiber ≅ uf ⋙ Phi.fiber) :
    Psi.sheafFiber (A := Type u) ≅ L ⋙ Phi.sheafFiber :=
  sheafFiberIsoOfFiberIso Psi e ≪≫
    sheafFiberIsoOfAdj Phi uf adj (pointOfFiberIso Psi e) rfl

end Transport

end Stacks.SitePointFiberIso

end
