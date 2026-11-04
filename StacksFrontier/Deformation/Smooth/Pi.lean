module

public import StacksFrontier.Deformation.BaseCategory.Pi
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.TangentSpace.Predeformation
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClasses

/-!
# Products over the base: isomorphism classes, smoothness and the differential

The chain of **Stacks 0DZF** passes from a single deformation category to finite products of
them, and each of its three maps is a product of maps of the factors. This file shows that the
two properties the tag asserts are detected factorwise on such a product: a product over the
base of smooth based functors is smooth, and a product of based functors each of which is
bijective on fibrewise isomorphism classes is again bijective — in particular on tangent spaces,
which are those classes at the dual numbers.

## Main results

* `Deformation.piMap_isSmooth_of_components`: `Deformation.piMap` of a family of smooth based
  functors is smooth.
* `Deformation.piMap_mapIsomorphismClasses_bijective`: `Deformation.piMap` of a family of based
  functors which are bijective on fibrewise isomorphism classes over an object `A` is bijective
  on isomorphism classes over `A`.
* `Deformation.bijective_differential_piMap_of_components`: the previous result at the dual
  numbers, i.e. a product of based functors inducing isomorphisms on tangent spaces induces an
  isomorphism on tangent spaces.
* `Deformation.piBasedCategory_isPredeformationCategory`: a product over the base of
  predeformation categories is a predeformation category.
* `Deformation.mapIsomorphismClasses_comp`: the map on isomorphism classes of a composite is the
  composite of the maps, which is what turns a statement about a composite of the chain into one
  about its legs.

## Implementation notes

`Deformation.classOf_eq_iff_nonempty_iso` is the bridge used throughout: equality of fibrewise
isomorphism classes is exactly the existence of an isomorphism in the fibre. It is stated with a
bare `Nonempty (x ≅ y)` rather than `CategoryTheory.IsIsomorphic` because it is used in both
directions, and the reverse direction is what builds an isomorphism of the product out of
isomorphisms of the factors in `Deformation.piFiber_nonempty_iso_of_components`.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 06HG](https://stacks.math.columbia.edu/tag/06HG)
* [Stacks Project, Tag 07W5](https://stacks.math.columbia.edu/tag/07W5)
-/

@[expose] public section

open CategoryTheory

universe uι u w v₁ u₁ v₂ u₂ v₃ u₃

namespace Deformation

/-! ### Isomorphism classes of a product over the base -/

/-- Two objects of a fibre have the same fibrewise isomorphism class exactly when they are
isomorphic in the fibre. -/
public theorem classOf_eq_iff_nonempty_iso
    {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝓕 : BasedCategory.{v₂, u₂} 𝒮}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) {A : 𝒮} (x y : 𝓕.p.Fiber A) :
    classOf 𝓕 h𝓕 x = classOf 𝓕 h𝓕 y ↔ Nonempty (x ≅ y) := by
  rw [← (Equiv.cast (isomorphismClasses_obj 𝓕 h𝓕 A)).injective.eq_iff]
  simp only [Equiv.cast_apply, classOf_eq, Quotient.eq]
  rfl

/-- An isomorphism in a fibre of a product over the base is the same thing as an isomorphism in
each factor over the identity. -/
public theorem piFiber_nonempty_iso_of_components
    {ι : Type uι} {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝓖 : ι → BasedCategory.{v₂, u₂} 𝒮) {A : 𝒮}
    (x y : (piBasedCategory 𝓖).p.Fiber A)
    (h : ∀ i, Nonempty
      ((fiberFunctor (piProj 𝓖 i) A).obj x ≅ (fiberFunctor (piProj 𝓖 i) A).obj y)) :
    Nonempty (x ≅ y) := by
  rcases x with ⟨⟨a, x, hx⟩, rfl⟩
  rcases y with ⟨⟨b, y, hy⟩, hb⟩
  change b = a at hb
  subst b
  let e i := Classical.choice (h i)
  let f : PiOver.Hom ⟨a, x, hx⟩ ⟨a, y, hy⟩ :=
    { hbase := 𝟙 a
      component i := (e i).hom.val
      hcomponent i := (e i).hom.property }
  let g : PiOver.Hom ⟨a, y, hy⟩ ⟨a, x, hx⟩ :=
    { hbase := 𝟙 a
      component i := (e i).inv.val
      hcomponent i := (e i).inv.property }
  refine ⟨{ hom := ⟨f, ?_⟩, inv := ⟨g, ?_⟩, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · exact IsHomLift.map (piBasedCategory 𝓖).p f
  · exact IsHomLift.map (piBasedCategory 𝓖).p g
  · exact Subtype.ext <| PiOver.Hom.ext' (Category.id_comp _) fun i ↦
      congrArg Subtype.val (e i).hom_inv_id
  · exact Subtype.ext <| PiOver.Hom.ext' (Category.id_comp _) fun i ↦
      congrArg Subtype.val (e i).inv_hom_id

/-- **A product over the base of bijections on isomorphism classes is a bijection.** If each
`φ i` induces a bijection on fibrewise isomorphism classes over `A`, so does the induced based
functor `Deformation.piMap φ` of the products. -/
public theorem piMap_mapIsomorphismClasses_bijective
    {ι : Type uι} {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝓖 : ι → BasedCategory.{v₂, u₂} 𝒮} {𝓗 : ι → BasedCategory.{v₃, u₃} 𝒮}
    (h𝓖 : ∀ i, IsCofiberedInGroupoids (𝓖 i).p)
    (h𝓗 : ∀ i, IsCofiberedInGroupoids (𝓗 i).p)
    (φ : ∀ i, BasedFunctor (𝓖 i) (𝓗 i)) (A : 𝒮)
    (hφ : ∀ i, Function.Bijective (mapIsomorphismClasses (h𝓖 i) (h𝓗 i) (φ i) A)) :
    Function.Bijective
      (mapIsomorphismClasses (piBasedCategory_isCofiberedInGroupoids 𝓖 h𝓖)
        (piBasedCategory_isCofiberedInGroupoids 𝓗 h𝓗) (piMap φ) A) := by
  let hG := piBasedCategory_isCofiberedInGroupoids 𝓖 h𝓖
  let hH := piBasedCategory_isCofiberedInGroupoids 𝓗 h𝓗
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := classOf_surjective _ hG A a
    obtain ⟨y, rfl⟩ := classOf_surjective _ hG A b
    rw [mapIsomorphismClasses_classOf, mapIsomorphismClasses_classOf] at hab
    obtain ⟨e⟩ := (classOf_eq_iff_nonempty_iso hH _ _).mp hab
    refine (classOf_eq_iff_nonempty_iso hG _ _).mpr <|
      piFiber_nonempty_iso_of_components _ _ _ fun i ↦
        (classOf_eq_iff_nonempty_iso (h𝓖 i) _ _).mp <| (hφ i).injective ?_
    rw [mapIsomorphismClasses_classOf, mapIsomorphismClasses_classOf]
    exact (classOf_eq_iff_nonempty_iso (h𝓗 i) _ _).mpr ⟨(fiberFunctor (piProj 𝓗 i) A).mapIso e⟩
  · intro b
    obtain ⟨y, rfl⟩ := classOf_surjective _ hH A b
    have hx : ∀ i, ∃ x : (𝓖 i).p.Fiber A,
        Nonempty ((fiberFunctor (φ i) A).obj x ≅ (fiberFunctor (piProj 𝓗 i) A).obj y) := by
      intro i
      obtain ⟨a, ha⟩ := (hφ i).surjective
        (classOf _ (h𝓗 i) ((fiberFunctor (piProj 𝓗 i) A).obj y))
      obtain ⟨x, rfl⟩ := classOf_surjective _ (h𝓖 i) A a
      rw [mapIsomorphismClasses_classOf] at ha
      exact ⟨x, (classOf_eq_iff_nonempty_iso (h𝓗 i) _ _).mp ha⟩
    choose x hx using hx
    let X : (piBasedCategory 𝓖).p.Fiber A :=
      ⟨⟨A, fun i ↦ (x i).val, fun i ↦ (x i).property⟩, rfl⟩
    refine ⟨classOf _ hG X, ?_⟩
    rw [mapIsomorphismClasses_classOf]
    exact (classOf_eq_iff_nonempty_iso hH _ _).mpr (piFiber_nonempty_iso_of_components _ _ _ hx)

/-! ### Predeformation categories, smoothness and the differential -/

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A product over the base of predeformation categories is a predeformation category: its
fibre over the residue field is the product of the one-object fibres. -/
public theorem piBasedCategory_isPredeformationCategory
    {ι : Type uι} (𝓖 : ι → BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓖 : ∀ i, IsPredeformationCategory (𝓖 i).p) :
    IsPredeformationCategory (piBasedCategory 𝓖).p := by
  refine ⟨piBasedCategory_isCofiberedInGroupoids 𝓖 (fun i ↦ (h𝓖 i).cofibered), ?_⟩
  let A := residueFieldObject Λ k
  let e i := Classical.choice (h𝓖 i).specialFiber
  let x i := (e i).inverse.obj ⟨PUnit.unit⟩
  apply (equiv_punit_iff_unique _).mpr
  refine ⟨⟨⟨⟨A, fun i ↦ (x i).val, fun i ↦ (x i).property⟩, rfl⟩⟩, ?_⟩
  intro X Y
  have huniq (i) : Nonempty (Unique
      (((fiberFunctor (piProj 𝓖 i) A).obj X) ⟶ ((fiberFunctor (piProj 𝓖 i) A).obj Y))) :=
    ((equiv_punit_iff_unique _).mp (h𝓖 i).specialFiber).2 _ _
  obtain ⟨d⟩ := piFiber_nonempty_iso_of_components 𝓖 X Y (fun i ↦
    ⟨(e i).functor.preimageIso (eqToIso (Subsingleton.elim _ _))⟩)
  refine ⟨{ default := d.hom, uniq := fun g ↦ Subtype.ext <| PiOver.Hom.ext' ?_ fun i ↦ ?_ }⟩
  · let := g.property
    let := d.hom.property
    exact (IsHomLift.fac' (piBasedCategory 𝓖).p (𝟙 A) g.val).trans
      (IsHomLift.fac' (piBasedCategory 𝓖).p (𝟙 A) d.hom.val).symm
  · let := Classical.choice (huniq i)
    exact congrArg Subtype.val (Subsingleton.elim
      ((fiberFunctor (piProj 𝓖 i) A).map g) ((fiberFunctor (piProj 𝓖 i) A).map d.hom))

/-- **A product over the base of smooth based functors is smooth.** A lifting problem for
`Deformation.piMap φ` is a base morphism together with one lifting problem in each factor; the
solutions are assembled componentwise. -/
public theorem piMap_isSmooth_of_components
    {ι : Type uι}
    {𝓖 : ι → BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓗 : ι → BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (φ : ∀ i, BasedFunctor (𝓖 i) (𝓗 i)) (hφ : ∀ i, IsSmooth (φ i)) :
    IsSmooth (piMap (ι := ι) φ) := by
  intro B A f hf y x g hg
  change (PiOver.structureFunctor (fun i ↦ (𝓗 i).p)).IsHomLift f g at hg
  let F := piMap (ι := ι) φ
  let x₀ : PiOver (fun i ↦ (𝓖 i).p) := x
  let y₀ : PiOver (fun i ↦ (𝓗 i).p) := y
  let : (PiOver.structureFunctor (fun i ↦ (𝓗 i).p)).IsHomLift f g := hg
  have hB : y₀.base = B :=
    IsHomLift.domain_eq (PiOver.structureFunctor (fun i ↦ (𝓗 i).p)) f g
  subst B
  have hA : (F.obj x₀).base = A :=
    IsHomLift.codomain_eq (PiOver.structureFunctor (fun i ↦ (𝓗 i).p)) f g
  subst A
  have hbase : f = g.hbase := by
    simpa [PiOver.structureFunctor] using
      @IsHomLift.eq_of_isHomLift _ _ _ _ (PiOver.structureFunctor fun i ↦ (𝓗 i).p) y (F.obj x)
        f g hg
  subst f
  have hsol : ∀ i, ∃ (x' : (𝓖 i).obj) (h : x' ⟶ x₀.x i) (a : (φ i).obj x' ⟶ y₀.x i),
      (𝓖 i).p.IsHomLift g.hbase h ∧
        (𝓗 i).p.IsHomLift (𝟙 y₀.base) a ∧ (φ i).map h = a ≫ g.component i := fun i ↦
    hφ i g.hbase hf (y₀.x i) (x₀.x i) (g.component i) (g.hcomponent i)
  choose x' h a hh ha hfac using hsol
  let X' : PiOver (fun i ↦ (𝓖 i).p) :=
    { base := y₀.base
      x := x'
      hx := fun i ↦ IsHomLift.domain_eq (𝓖 i).p g.hbase (h i) }
  let h' : X' ⟶ x₀ :=
    { hbase := g.hbase
      component := h
      hcomponent := hh }
  let a' : F.obj X' ⟶ y₀ :=
    { hbase := 𝟙 y₀.base
      component := a
      hcomponent := ha }
  exact ⟨X', h', a', IsHomLift.map (piBasedCategory 𝓖).p h',
    IsHomLift.map (piBasedCategory 𝓗).p a', PiOver.Hom.ext' rfl hfac⟩

/-- **A product over the base of tangent-space isomorphisms is a tangent-space isomorphism.**
This is `Deformation.piMap_mapIsomorphismClasses_bijective` at the dual numbers, where the
isomorphism classes are the tangent spaces. -/
public theorem bijective_differential_piMap_of_components
    {ι : Type uι}
    {𝓖 : ι → BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓗 : ι → BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓖 : ∀ i, IsCofiberedInGroupoids (𝓖 i).p)
    (h𝓗 : ∀ i, IsCofiberedInGroupoids (𝓗 i).p)
    (φ : ∀ i, BasedFunctor (𝓖 i) (𝓗 i))
    (hφ : ∀ i, Function.Bijective (differential (h𝓖 i) (h𝓗 i) (φ i))) :
    Function.Bijective
      (differential (piBasedCategory_isCofiberedInGroupoids 𝓖 h𝓖)
        (piBasedCategory_isCofiberedInGroupoids 𝓗 h𝓗) (piMap φ)) :=
  piMap_mapIsomorphismClasses_bijective h𝓖 h𝓗 φ
    (augmentedDualNumbers (Λ := Λ) (k := k)) hφ

end

end Deformation
