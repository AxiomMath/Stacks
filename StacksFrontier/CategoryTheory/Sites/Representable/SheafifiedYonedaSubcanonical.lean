module

public import Mathlib.CategoryTheory.Sites.Canonical
public import StacksFrontier.CategoryTheory.Sites.Density
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheafified Yoneda embedding of a subcanonical site, and uniqueness of representing objects

On a site whose topology is subcanonical a representable presheaf is already a sheaf, so the
sheafified Yoneda embedding `U ↦ h_U^#` of `CategoryTheory.Sheaf.sheafifiedYoneda` agrees with
Mathlib's Yoneda embedding into sheaves, `CategoryTheory.GrothendieckTopology.uliftYoneda`, and
is therefore fully faithful.

Consequently an object representing a given sheaf is unique up to a *unique* isomorphism, so a
family of representing objects of one sheaf carries a canonical family of transition
isomorphisms, and those transitions satisfy the cocycle condition automatically.

## Main definitions

* `CategoryTheory.Sheaf.uliftYonedaIsoSheafifiedYoneda` — the comparison with Mathlib's Yoneda
  embedding into sheaves on a subcanonical site, in the direction
  `uliftYoneda J ≅ sheafifiedYoneda J`.
* `CategoryTheory.Sheaf.fullyFaithfulSheafifiedYoneda` — the sheafified Yoneda embedding of a
  subcanonical site is fully faithful.
* `CategoryTheory.Sheaf.representingIso` — the isomorphism of objects underlying an isomorphism
  of the sheafified representables they represent.
* `CategoryTheory.Sheaf.transition` — the transition isomorphism between two members of a family
  of objects all representing one sheaf.

## Main results

* `CategoryTheory.Sheaf.representingIso_unique` — a morphism of objects inducing a given
  morphism of sheafified representables is unique, which is the uniqueness half of "unique up to
  unique isomorphism".
* `CategoryTheory.Sheaf.transition_self`, `CategoryTheory.Sheaf.transition_trans`,
  `CategoryTheory.Sheaf.transition_symm` — the transitions of a family of representing objects
  are normalized, cocyclic and symmetric. In particular the cocycle condition needs no
  hypothesis: it is a consequence of faithfulness.

## Implementation notes

`CategoryTheory.Sheaf.sheafifiedYoneda J` is `uliftYoneda ⋙ presheafToSheaf J` and
`CategoryTheory.GrothendieckTopology.uliftYoneda J` is the lift of the same presheaf-valued
functor through `sheafToPresheaf`, the lift existing exactly because the topology is
subcanonical. The two therefore differ by one application of sheafification to something already
a sheaf, and `CategoryTheory.sheafificationIso` is that comparison; its naturality is the
naturality of `CategoryTheory.toSheafify`.

The transition isomorphisms are indexed by a family `e i : h_{U i}^# ≅ F` of presentations of
one sheaf rather than by `F ≅ h_{U i}`, which is the direction a gluing argument produces them
in; `transition e i j` is the preimage under the embedding of `e i ≪≫ (e j).symm`.

## References

* [Stacks Project, Tag 00WR](https://stacks.math.columbia.edu/tag/00WR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type max u v)] [J.Subcanonical]

/-- **On a subcanonical site the sheafified Yoneda embedding is the Yoneda embedding.** The
presheaf represented by an object is already a sheaf, so sheafifying it changes nothing. -/
@[sga "4 II 4.4.0" "partial"]
def uliftYonedaIsoSheafifiedYoneda :
    GrothendieckTopology.uliftYoneda.{u} J ≅ sheafifiedYoneda J :=
  NatIso.ofComponents
    (fun X ↦ sheafificationIso ((GrothendieckTopology.uliftYoneda.{u} J).obj X))
    fun f ↦ Sheaf.hom_ext (toSheafify_naturality J (uliftYoneda.{u}.map f))

/-- **The sheafified Yoneda embedding of a subcanonical site is fully faithful.** A morphism
`h_U^# ⟶ h_V^#` of sheaves comes from a unique morphism `U ⟶ V` of the site. -/
def fullyFaithfulSheafifiedYoneda : (sheafifiedYoneda J).FullyFaithful :=
  J.fullyFaithfulUliftYoneda.ofIso (uliftYonedaIsoSheafifiedYoneda J)

/-- The sheafified Yoneda embedding of a subcanonical site is full. -/
instance sheafifiedYoneda_full : (sheafifiedYoneda J).Full :=
  (fullyFaithfulSheafifiedYoneda J).full

/-- The sheafified Yoneda embedding of a subcanonical site is faithful. -/
instance sheafifiedYoneda_faithful : (sheafifiedYoneda J).Faithful :=
  (fullyFaithfulSheafifiedYoneda J).faithful

/-! ### Uniqueness of a representing object -/

variable {J}

/-- The morphism of objects of the site underlying a morphism of the sheaves they represent. -/
def representingHom {U U' : C} (φ : (sheafifiedYoneda J).obj U ⟶ (sheafifiedYoneda J).obj U') :
    U ⟶ U' :=
  (fullyFaithfulSheafifiedYoneda J).preimage φ

/-- The sheafified Yoneda embedding sends `representingHom φ` to `φ`. -/
@[simp]
theorem map_representingHom {U U' : C}
    (φ : (sheafifiedYoneda J).obj U ⟶ (sheafifiedYoneda J).obj U') :
    (sheafifiedYoneda J).map (representingHom φ) = φ :=
  (fullyFaithfulSheafifiedYoneda J).map_preimage φ

/-- A morphism of the site inducing a given morphism of sheafified representables is unique. -/
theorem representingHom_unique {U U' : C}
    {φ : (sheafifiedYoneda J).obj U ⟶ (sheafifiedYoneda J).obj U'} {f : U ⟶ U'}
    (hf : (sheafifiedYoneda J).map f = φ) : f = representingHom φ :=
  (fullyFaithfulSheafifiedYoneda J).map_injective (hf.trans (map_representingHom φ).symm)

/-- **A representing object is unique up to isomorphism.** An isomorphism of the sheaves
represented by two objects of a subcanonical site comes from an isomorphism of those objects. -/
@[ega "III 7.4.6" "partial"]
def representingIso {U U' : C} (e : (sheafifiedYoneda J).obj U ≅ (sheafifiedYoneda J).obj U') :
    U ≅ U' :=
  (fullyFaithfulSheafifiedYoneda J).preimageIso e

/-- The sheafified Yoneda embedding sends `(representingIso e).hom` to `e.hom`. -/
@[simp]
theorem map_representingIso_hom {U U' : C}
    (e : (sheafifiedYoneda J).obj U ≅ (sheafifiedYoneda J).obj U') :
    (sheafifiedYoneda J).map (representingIso e).hom = e.hom :=
  (fullyFaithfulSheafifiedYoneda J).map_preimage e.hom

/-- The sheafified Yoneda embedding sends `(representingIso e).inv` to `e.inv`. -/
@[simp]
theorem map_representingIso_inv {U U' : C}
    (e : (sheafifiedYoneda J).obj U ≅ (sheafifiedYoneda J).obj U') :
    (sheafifiedYoneda J).map (representingIso e).inv = e.inv :=
  (fullyFaithfulSheafifiedYoneda J).map_preimage e.inv

/-- **A representing object is unique up to a unique isomorphism.** -/
@[ega "III 7.4.6" "partial"]
theorem representingIso_unique {U U' : C}
    {e : (sheafifiedYoneda J).obj U ≅ (sheafifiedYoneda J).obj U'} {f : U ≅ U'}
    (hf : (sheafifiedYoneda J).map f.hom = e.hom) : f = representingIso e :=
  Iso.ext (representingHom_unique hf)

/-! ### The transition isomorphisms of a family of representing objects -/

section Transition

variable {ι : Type w} {F : Sheaf J (Type max u v)} {U : ι → C}
  (e : ∀ i, (sheafifiedYoneda J).obj (U i) ≅ F)

/-- **The transition isomorphism.** Given a family of objects of the site each representing one
and the same sheaf `F`, the transition from the `i`-th to the `j`-th is the isomorphism of
objects underlying the comparison of the two presentations. It is forced by `F`: no choice
enters, by `CategoryTheory.Sheaf.representingIso_unique`. -/
def transition (i j : ι) : U i ≅ U j :=
  representingIso (e i ≪≫ (e j).symm)

/-- The sheafified Yoneda embedding sends `(transition e i j).hom` to `(e i).hom ≫ (e j).inv`. -/
@[simp]
theorem map_transition_hom (i j : ι) :
    (sheafifiedYoneda J).map (transition e i j).hom = (e i).hom ≫ (e j).inv :=
  map_representingIso_hom _

/-- The sheafified Yoneda embedding sends `(transition e i j).inv` to `(e j).hom ≫ (e i).inv`. -/
@[simp]
theorem map_transition_inv (i j : ι) :
    (sheafifiedYoneda J).map (transition e i j).inv = (e j).hom ≫ (e i).inv :=
  map_representingIso_inv _

/-- The transition from a presentation to itself is the identity. -/
@[simp]
theorem transition_self (i : ι) : transition e i i = Iso.refl (U i) :=
  ((representingIso_unique (e := e i ≪≫ (e i).symm) (f := Iso.refl (U i)) (by
    rw [Iso.refl_hom, Functor.map_id, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id])).symm)

/-- **The cocycle condition.** The transitions of a family of objects representing one sheaf
compose: the transition from `i` to `j` followed by that from `j` to `k` is the transition from
`i` to `k`. -/
theorem transition_trans (i j k : ι) :
    (transition e i j).hom ≫ (transition e j k).hom = (transition e i k).hom :=
  (fullyFaithfulSheafifiedYoneda J).map_injective (by
    rw [Functor.map_comp, map_transition_hom, map_transition_hom, map_transition_hom,
      Category.assoc, Iso.inv_hom_id_assoc])

/-- The transitions of a family of objects representing one sheaf are symmetric. -/
theorem transition_symm (i j : ι) : (transition e i j).symm = transition e j i :=
  Iso.ext ((fullyFaithfulSheafifiedYoneda J).map_injective (by
    rw [Iso.symm_hom, map_transition_inv, map_transition_hom]))

end Transition

end CategoryTheory.Sheaf

end
