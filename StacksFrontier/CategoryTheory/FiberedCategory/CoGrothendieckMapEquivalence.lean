module

public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence

/-!
# The CoGrothendieck construction of an isomorphism is an equivalence over the base

Let `F` and `G` be pseudofunctors from the locally discrete bicategory on `𝒮ᵒᵖ` to `Cat`, and let
`α : F ⟶ G` be a strong transformation whose every component `α.app a : F.obj a ⟶ G.obj a` is an
*isomorphism of categories*. Then the functor `CategoryTheory.Pseudofunctor.CoGrothendieck.map α`
it induces between the total categories of the CoGrothendieck construction is an *equivalence over
`𝒮`* in the sense of `CategoryTheory.Functor.IsEquivalenceOver`: it commutes strictly with the two
projections, and its quasi-inverse does too, with vertical unit and counit.

This is what lets a presentation of a fibred category by a presheaf of categories — or of
groupoids, through `CategoryTheory.presheafOfGroupoids` — be replaced by an isomorphic one before a
result stated for the other presentation is applied. Stacks 05YQ needs exactly that: the two
clauses of Stacks 02ZN are proved there for the pointwise groupoid fibration of the presheaf `FA_d`
of free rank-`d` algebra structures, while the recognition criterion for the quotient stack asks
for them on the pointwise groupoid fibration of the action groupoid of the conjugation action, and
the two presheaves of groupoids are isomorphic rather than equal.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.faithful_map` and
  `CategoryTheory.Pseudofunctor.CoGrothendieck.full_map`: the induced functor is fully faithful as
  soon as every component of `α` is.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.hasVerticalPreimages_map`: every object of the
  target is, over an identity of `𝒮`, isomorphic to an image.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.isEquivalenceOver_map`: the three together, in the
  form `CategoryTheory.Functor.IsEquivalenceOver`.

## Implementation notes

A morphism of `∫ᶜ F` is a pair of a morphism `base` of `𝒮` and a morphism `fiber` of a value of
`F`, whose type mentions `base`; so an equality of two such morphisms is not the conjunction of two
equalities but an equality of the bases together with a *heterogeneous* equality of the fibres.
Mathlib's `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext` states it with the second equality
transported by an `eqToHom`, which is the convenient form when the two bases are merely equal;
`CategoryTheory.Pseudofunctor.CoGrothendieck.hom_ext_heq` below is the form used here, where the
two bases are *definitionally* equal and the transport would only have to be cancelled again.

The cancellation of the comparison isomorphism in `full_map` is done by the auxiliary
`CategoryTheory.Pseudofunctor.CoGrothendieck.comp_inv_hom_app` and not inline, because inline the
goal mentions `((map α).obj a).base` where the ambient type expects `a.base`: the two are
definitionally equal but not syntactically, and `rw` refuses such a goal as not type-correct at
`implicit` transparency.

The hypothesis is that each component of `α` is an isomorphism of `Cat`, that is an isomorphism of
categories and not merely an equivalence. That is what holds for the natural isomorphisms this is
applied to — a natural isomorphism of presheaves of groupoids has isomorphisms of groupoids for its
components — and it is what makes the quasi-inverse of each component strict, hence the preimages
of `hasVerticalPreimages_map` equalities rather than isomorphisms.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
-/

@[expose] public section

open CategoryTheory Opposite Pseudofunctor
open scoped Pseudofunctor.CoGrothendieck Pseudofunctor.StrongTrans

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {F G : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-! ### Extensionality in the heterogeneous form -/

/-- Two objects of `∫ᶜ F` with equal bases and heterogeneously equal fibres agree. -/
theorem obj_ext_heq {x y : ∫ᶜ F} (hb : x.base = y.base) (hf : HEq x.fiber y.fiber) : x = y := by
  obtain ⟨xb, xf⟩ := x
  obtain ⟨yb, yf⟩ := y
  obtain rfl : xb = yb := hb
  obtain rfl : xf = yf := eq_of_heq hf
  rfl

/-- Two morphisms of `∫ᶜ F` with equal bases and heterogeneously equal fibres agree. This is
`CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext` with no `eqToHom` transport, which is the
form to use when the two bases are definitionally equal. -/
theorem hom_ext_heq {a b : ∫ᶜ F} {f g : a ⟶ b} (hb : f.base = g.base)
    (hf : HEq f.fiber g.fiber) : f = g := by
  obtain ⟨fb, ff⟩ := f
  obtain ⟨gb, gf⟩ := g
  obtain rfl : fb = gb := hb
  obtain rfl : ff = gf := eq_of_heq hf
  rfl

/-- The fibres of the images of two equal morphisms of `∫ᶜ F` are heterogeneously equal. -/
theorem map_fiber_heq (α : F ⟶ G) {a b : ∫ᶜ F} {f g : a ⟶ b}
    (hfg : (map α).map f = (map α).map g) :
    HEq ((map α).map f).fiber ((map α).map g).fiber := by
  rw [hfg]

/-- Cancelling a component of a `2`-isomorphism of `Cat` against its inverse. -/
theorem comp_inv_hom_app {X Y : Cat.{v₂, u₂}} {P Q : X ⟶ Y} (i : P ≅ Q) (z : ↥X)
    {W : ↥Y} (x : W ⟶ Q.toFunctor.obj z) :
    (x ≫ i.inv.toNatTrans.app z) ≫ i.hom.toNatTrans.app z = x := by
  rw [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app, Category.comp_id]

/-! ### An isomorphism of categories is fully faithful -/

/-- The equivalence of categories underlying an isomorphism of `Cat`: a `1`-morphism of `Cat` with
a strict two-sided inverse. -/
noncomputable def catEquivOfStrictInverse {X Y : Cat.{v₂, u₂}} (P : X ⟶ Y) (Q : Y ⟶ X)
    (h₁ : P ≫ Q = 𝟙 X) (h₂ : Q ≫ P = 𝟙 Y) : ↥X ≌ ↥Y :=
  Equivalence.mk P.toFunctor Q.toFunctor
    (eqToIso (show P.toFunctor ⋙ Q.toFunctor = 𝟭 ↥X by
      rw [← Cat.Hom.comp_toFunctor, h₁, Cat.Hom.id_toFunctor])).symm
    (eqToIso (show Q.toFunctor ⋙ P.toFunctor = 𝟭 ↥Y by
      rw [← Cat.Hom.comp_toFunctor, h₂, Cat.Hom.id_toFunctor]))

/-- An isomorphism of `Cat` is an equivalence of categories. -/
private theorem isEquivalence_of_isIso {X Y : Cat.{v₂, u₂}} (P : X ⟶ Y) [IsIso P] :
    P.toFunctor.IsEquivalence :=
  (catEquivOfStrictInverse P (inv P) (IsIso.hom_inv_id P)
    (IsIso.inv_hom_id P)).isEquivalence_functor

/-- An isomorphism of `Cat` is a full functor. -/
theorem full_of_isIso {X Y : Cat.{v₂, u₂}} (P : X ⟶ Y) [IsIso P] : P.toFunctor.Full :=
  haveI := isEquivalence_of_isIso P
  inferInstance

/-- An isomorphism of `Cat` is a faithful functor. -/
theorem faithful_of_isIso {X Y : Cat.{v₂, u₂}} (P : X ⟶ Y) [IsIso P] : P.toFunctor.Faithful :=
  haveI := isEquivalence_of_isIso P
  inferInstance

/-- The object map of an isomorphism of `Cat` is undone by that of its inverse. -/
theorem obj_inv_obj {X Y : Cat.{v₂, u₂}} (P : X ⟶ Y) [IsIso P] (y : ↥Y) :
    P.toFunctor.obj ((inv P).toFunctor.obj y) = y :=
  Functor.congr_obj (show (inv P).toFunctor ⋙ P.toFunctor = 𝟭 ↥Y by
    rw [← Cat.Hom.comp_toFunctor, IsIso.inv_hom_id P, Cat.Hom.id_toFunctor]) y

/-! ### The induced functor is fully faithful -/

/-- **The functor induced on the CoGrothendieck constructions is faithful** as soon as every
component of the strong transformation is: the bases of two morphisms with the same image agree,
and after cancelling the comparison isomorphism so do the images of the fibres. -/
theorem faithful_map (α : F ⟶ G) (hfaith : ∀ a, (α.app a).toFunctor.Faithful) :
    (map α).Faithful where
  map_injective {a b} f g hfg := by
    have hb : f.base = g.base := by
      rw [← map_map_base α f, ← map_map_base α g, hfg]
    obtain ⟨fb, ff⟩ := f
    obtain ⟨gb, gf⟩ := g
    obtain rfl : fb = gb := hb
    have hfib : ((map α).map (Hom.mk fb ff)).fiber =
        ((map α).map (Hom.mk fb gf)).fiber := eq_of_heq (map_fiber_heq α hfg)
    rw [map_map_fiber, map_map_fiber] at hfib
    refine hom_ext_heq rfl (heq_of_eq ?_)
    have := hfaith { as := op a.base }
    exact (α.app { as := op a.base }).toFunctor.map_injective ((cancel_mono _).mp hfib)

/-- **The functor induced on the CoGrothendieck constructions is full** as soon as every component
of the strong transformation is fully faithful: a morphism of the target is the image of the one
whose base it already is and whose fibre is the preimage of its fibre, conjugated by the comparison
isomorphism. -/
theorem full_map (α : F ⟶ G) (hfull : ∀ a, (α.app a).toFunctor.Full)
    (hfaith : ∀ a, (α.app a).toFunctor.Faithful) : (map α).Full where
  map_surjective {a b} ψ := by
    have := hfull { as := op a.base }
    have := hfaith { as := op a.base }
    refine ⟨Hom.mk ψ.base
      ((Functor.FullyFaithful.ofFullyFaithful (α.app { as := op a.base }).toFunctor).preimage
        (ψ.fiber ≫ (α.naturality ψ.base.op.toLoc).inv.toNatTrans.app b.fiber)),
      hom_ext_heq rfl (heq_of_eq ?_)⟩
    rw [map_map_fiber, Functor.FullyFaithful.map_preimage]
    exact comp_inv_hom_app (α.naturality ψ.base.op.toLoc) b.fiber ψ.fiber

/-! ### Vertical preimages -/

/-- **Every object of the target CoGrothendieck construction is the image of an object over the
same object of `𝒮`**, when every component of the strong transformation is an isomorphism of
categories: the preimage of the fibre under the inverse component has the given fibre for its
image, so the comparison is an equality and the isomorphism an `eqToIso`, which lies over an
identity. -/
theorem hasVerticalPreimages_map (α : F ⟶ G) (hiso : ∀ a, IsIso (α.app a)) :
    Functor.HasVerticalPreimages (forget F) (forget G) (map α) := by
  intro y
  have := hiso { as := op y.base }
  have he : y = (map α).obj
      ⟨y.base, (inv (α.app { as := op y.base })).toFunctor.obj y.fiber⟩ :=
    obj_ext_heq rfl (heq_of_eq (obj_inv_obj (α.app { as := op y.base }) y.fiber).symm)
  exact ⟨_, rfl, eqToIso he, IsHomLift.eqToHom_domain_lift_id he rfl⟩

/-! ### The equivalence over the base -/

/-- **The functor induced on the CoGrothendieck constructions by a strong transformation whose
components are isomorphisms of categories is an equivalence over `𝒮`.** It is fully faithful and
has vertical preimages, and it commutes strictly with the two projections, so
`CategoryTheory.Functor.isEquivalenceOver_of_exists_vertical_iso` applies. -/
noncomputable def isEquivalenceOver_map (α : F ⟶ G) (hiso : ∀ a, IsIso (α.app a)) :
    Functor.IsEquivalenceOver (forget F) (forget G) (map α) :=
  haveI hfull : ∀ a, (α.app a).toFunctor.Full :=
    fun a => haveI := hiso a; full_of_isIso (α.app a)
  haveI hfaith : ∀ a, (α.app a).toFunctor.Faithful :=
    fun a => haveI := hiso a; faithful_of_isIso (α.app a)
  haveI := full_map α hfull hfaith
  haveI := faithful_map α hfaith
  Functor.isEquivalenceOver_of_exists_vertical_iso (map_comp_forget α)
    (hasVerticalPreimages_map α hiso)

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
