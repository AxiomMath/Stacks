module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.Deformation.Cofibered

/-!
# The product over the base of a family of categories over a base

A finite product of deformation categories, in the sense in which **Stacks 0DZF** forms
`∏ 𝓓_{P_{𝔪 i}}`, is the product *over* the base category `𝒞_Λ`: an object is a single base object
together with one object of each factor lying over it, and a morphism is a single base morphism
together with a lift of it in every factor. This is the fibre product over `𝒞_Λ` regarded as a
deformation category over itself, which is the reading the proof of Stacks 0DZN records.

This file builds that product for an arbitrary family of categories over an arbitrary base
category, indexed by an arbitrary type — finiteness of the index is a hypothesis of the lemmas
that use it, not of the construction — and shows that it inherits being cofibered in groupoids
from its factors.

## Main definitions

* `Deformation.PiOver`: the product over `𝒞` of a family of categories over `𝒞`.
* `Deformation.PiOver.structureFunctor`, `Deformation.PiOver.proj`, `Deformation.PiOver.lift`:
  its structure functor to `𝒞`, its projections to the factors, and the functor into it
  determined by a family of functors over `𝒞` with common source.
* `Deformation.piBasedCategory`, `Deformation.piProj`, `Deformation.piLift`,
  `Deformation.piMap`: the same for based categories over `𝒞`, the last being the based functor
  between two such products induced by a family of based functors between the factors.

## Main results

* `Deformation.piBasedCategory_isCofiberedInGroupoids`: a product over the base of categories
  cofibered in groupoids is cofibered in groupoids.

## Implementation notes

An object of `Deformation.PiOver` carries the *equations* `(p i).obj (x i) = base` rather than
being a tuple in a fibre, so that the structure functor to `𝒞` is a strict functor and the
projections are strictly over `𝒞`; this is what lets the construction be used as a based
category with no coherence data.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DZN](https://stacks.math.columbia.edu/tag/0DZN)
-/

@[expose] public section

open CategoryTheory

universe uι v₁ u₁ v₂ u₂ v₃ u₃

namespace Deformation

/-! ### The product over a base category -/

/-- An object of the product over `𝒞` of a family `X` of categories over `𝒞`: an object `base`
of `𝒞` together with an object of each factor lying over it. -/
public structure PiOver {ι : Type uι} {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {X : ι → Type u₂} [∀ i, Category.{v₂} (X i)] (p : ∀ i, X i ⥤ 𝒞) where
  /-- The common base object. -/
  base : 𝒞
  /-- The object of the `i`-th factor. -/
  x : ∀ i, X i
  /-- Each `x i` lies over `base`. -/
  hx : ∀ i, (p i).obj (x i) = base

namespace PiOver

variable {ι : Type uι} {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : ι → Type u₂}
  [∀ i, Category.{v₂} (X i)] {p : ∀ i, X i ⥤ 𝒞}

/-- A morphism of the product over `𝒞`: a morphism of base objects together with a lift of it in
every factor. -/
@[ext]
public structure Hom (P Q : PiOver p) where
  /-- The morphism of base objects. -/
  hbase : P.base ⟶ Q.base
  /-- The component in the `i`-th factor. -/
  component : ∀ i, P.x i ⟶ Q.x i
  /-- Every component lies over the base morphism. -/
  hcomponent : ∀ i, (p i).IsHomLift hbase (component i)

/-- Extensionality in terms of the components one at a time. -/
public lemma Hom.ext' {P Q : PiOver p} {f g : Hom P Q} (hb : f.hbase = g.hbase)
    (hc : ∀ i, f.component i = g.component i) : f = g :=
  Hom.ext hb (funext hc)

/-- The identity morphism of the product over `𝒞`. -/
public def Hom.id (P : PiOver p) : Hom P P where
  hbase := 𝟙 P.base
  component i := 𝟙 (P.x i)
  hcomponent i := by rw [← P.hx i]; infer_instance

/-- Composition in the product over `𝒞`, componentwise. -/
public def Hom.comp {P Q R : PiOver p} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hbase := f.hbase ≫ g.hbase
  component i := f.component i ≫ g.component i
  hcomponent i := by
    have := f.hcomponent i
    have := g.hcomponent i
    infer_instance

/-- The product over `𝒞` is a category, with componentwise identities and composition. -/
public instance instCategory : Category (PiOver p) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext' <;> simp [Hom.id, Hom.comp]
  comp_id f := by apply Hom.ext' <;> simp [Hom.id, Hom.comp]
  assoc f g h := by apply Hom.ext' <;> simp [Hom.comp]

/-- The base morphism of an identity is the identity. -/
@[simp] public lemma id_hbase (P : PiOver p) : Hom.hbase (𝟙 P) = 𝟙 P.base := rfl

/-- Each component of an identity is the identity. -/
@[simp] public lemma id_component (P : PiOver p) (i : ι) :
    Hom.component (𝟙 P) i = 𝟙 (P.x i) := rfl

/-- The base morphism of a composite is the composite of the base morphisms. -/
@[simp] public lemma comp_hbase {P Q R : PiOver p} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).hbase = f.hbase ≫ g.hbase := rfl

/-- Each component of a composite is the composite of the components. -/
@[simp] public lemma comp_component {P Q R : PiOver p} (f : P ⟶ Q) (g : Q ⟶ R) (i : ι) :
    (f ≫ g).component i = f.component i ≫ g.component i := rfl

/-- The structure functor of the product over `𝒞`. -/
@[simps]
public def structureFunctor (p : ∀ i, X i ⥤ 𝒞) : PiOver p ⥤ 𝒞 where
  obj P := P.base
  map f := f.hbase

/-- The projection of the product over `𝒞` to its `i`-th factor. -/
@[simps]
public def proj (p : ∀ i, X i ⥤ 𝒞) (i : ι) : PiOver p ⥤ X i where
  obj P := P.x i
  map f := f.component i

/-- Every projection is strictly over `𝒞`. -/
public lemma proj_comp_eq (i : ι) : proj p i ⋙ p i = structureFunctor p := by
  refine CategoryTheory.Functor.ext (fun P ↦ P.hx i) ?_
  intro P Q f
  have := f.hcomponent i
  exact CategoryTheory.IsHomLift.fac' (p i) f.hbase (f.component i)

/-- The functor into the product over `𝒞` determined by a family of functors over `𝒞` with
common source. -/
@[simps]
public def lift {𝒟 : Type u₃} [Category.{v₃} 𝒟] (q : 𝒟 ⥤ 𝒞) (F : ∀ i, 𝒟 ⥤ X i)
    (hF : ∀ i, F i ⋙ p i = q) : 𝒟 ⥤ PiOver p where
  obj a := { base := q.obj a, x i := (F i).obj a, hx i := by rw [← hF i]; rfl }
  map {a b} f :=
    { hbase := q.map f
      component i := (F i).map f
      hcomponent i := Functor.isHomLift_map_of_comp_eq (hF i) (q.map f) f }
  map_id a := by apply Hom.ext' <;> simp
  map_comp f g := by apply Hom.ext' <;> simp

/-- The functor into the product over `𝒞` is strictly over `𝒞`. -/
public lemma lift_comp_eq {𝒟 : Type u₃} [Category.{v₃} 𝒟] (q : 𝒟 ⥤ 𝒞) (F : ∀ i, 𝒟 ⥤ X i)
    (hF : ∀ i, F i ⋙ p i = q) : lift q F hF ⋙ structureFunctor p = q := rfl

end PiOver

/-! ### The product of based categories -/

/-- The product over the base of a family of based categories. -/
public def piBasedCategory {ι : Type uι} {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝓖 : ι → BasedCategory.{v₂, u₂} 𝒮) :
    BasedCategory.{max uι v₂ v₁, max uι u₁ u₂} 𝒮 :=
  BasedCategory.ofFunctor (PiOver.structureFunctor (fun i ↦ (𝓖 i).p))

/-- The projection of the product of based categories to its `i`-th factor. -/
public def piProj {ι : Type uι} {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝓖 : ι → BasedCategory.{v₂, u₂} 𝒮) (i : ι) :
    BasedFunctor (piBasedCategory 𝓖) (𝓖 i) where
  toFunctor := PiOver.proj (fun i ↦ (𝓖 i).p) i
  w := PiOver.proj_comp_eq i

/-- The based functor into the product determined by a family of based functors with common
source. -/
public def piLift {ι : Type uι} {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝓕 : BasedCategory.{v₃, u₃} 𝒮} {𝓖 : ι → BasedCategory.{v₂, u₂} 𝒮}
    (φ : ∀ i, BasedFunctor 𝓕 (𝓖 i)) : BasedFunctor 𝓕 (piBasedCategory 𝓖) where
  toFunctor := PiOver.lift 𝓕.p (fun i ↦ (φ i).toFunctor) (fun i ↦ (φ i).w)
  w := PiOver.lift_comp_eq _ _ _

/-- The based functor between two products induced by a family of based functors between their
factors. -/
public def piMap {ι : Type uι} {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝓖 : ι → BasedCategory.{v₂, u₂} 𝒮} {𝓗 : ι → BasedCategory.{v₃, u₃} 𝒮}
    (φ : ∀ i, BasedFunctor (𝓖 i) (𝓗 i)) :
    BasedFunctor (piBasedCategory 𝓖) (piBasedCategory 𝓗) :=
  piLift (fun i ↦ BasedFunctor.comp (piProj 𝓖 i) (φ i))

/-- A product over the base of categories cofibered in groupoids is cofibered in groupoids: a
lift of a base morphism is chosen in each factor, and uniqueness of the lift of a commuting
triangle holds factorwise. -/
public theorem piBasedCategory_isCofiberedInGroupoids
    {ι : Type uι} {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝓖 : ι → BasedCategory.{v₂, u₂} 𝒮)
    (h𝓖 : ∀ i, IsCofiberedInGroupoids (𝓖 i).p) :
    IsCofiberedInGroupoids (piBasedCategory 𝓖).p := by
  show (PiOver.structureFunctor (fun i ↦ (𝓖 i).p)).op.IsFiberedInGroupoids
  constructor
  · intro V U f x hx
    let x₀ : PiOver (fun i ↦ (𝓖 i).p) := Opposite.unop x
    have hxbase : x₀.base = Opposite.unop U := congrArg Opposite.unop hx
    have hcomponent : ∀ i, ∃ yi : (𝓖 i).objᵒᵖ, ∃ gi : yi ⟶ Opposite.op (x₀.x i),
        (𝓖 i).p.op.IsHomLift f gi := by
      intro i
      exact (h𝓖 i).exists_lift f (Opposite.op (x₀.x i))
        (congrArg Opposite.op ((x₀.hx i).trans hxbase))
    choose yi gi hgi using hcomponent
    let y : PiOver (fun i ↦ (𝓖 i).p) :=
      { base := Opposite.unop V
        x := fun i ↦ Opposite.unop (yi i)
        hx := fun i ↦ congrArg Opposite.unop (IsHomLift.domain_eq (𝓖 i).p.op f (gi i)) }
    let g : x₀ ⟶ y :=
      { hbase := eqToHom hxbase ≫ f.unop
        component := fun i ↦ (gi i).unop
        hcomponent := fun i ↦ by
          apply IsHomLift.of_fac' (𝓖 i).p (eqToHom hxbase ≫ f.unop) (gi i).unop
            (x₀.hx i) (y.hx i)
          simpa [Category.assoc, eqToHom_trans_assoc] using
            congrArg Quiver.Hom.unop (IsHomLift.fac' (𝓖 i).p.op f (gi i)) }
    refine ⟨Opposite.op y, g.op, ?_⟩
    refine IsHomLift.of_fac' (PiOver.structureFunctor (fun i ↦ (𝓖 i).p)).op f g.op ?_ hx ?_
    · exact Opposite.op_unop V
    · show (eqToHom hxbase ≫ f.unop).op =
        eqToHom (Opposite.op_unop V) ≫ f ≫ eqToHom hx.symm
      rw [CategoryTheory.op_comp, Quiver.Hom.op_unop]
      simp only [eqToHom_op, eqToHom_refl, Category.id_comp]
      congr 1
  · intro x y z φ ψ f hcomm
    let x₀ : PiOver (fun i ↦ (𝓖 i).p) := Opposite.unop x
    let y₀ : PiOver (fun i ↦ (𝓖 i).p) := Opposite.unop y
    let z₀ : PiOver (fun i ↦ (𝓖 i).p) := Opposite.unop z
    let φ₀ : x₀ ⟶ y₀ := φ.unop
    let ψ₀ : x₀ ⟶ z₀ := ψ.unop
    let f₀ : y₀.base ⟶ z₀.base := f.unop
    have hbase : φ₀.hbase ≫ f₀ = ψ₀.hbase :=
      Quiver.Hom.op_inj (by rw [CategoryTheory.op_comp]; exact hcomm)
    -- in each factor, the triangle to be lifted commutes
    have hcommi : ∀ i, (eqToHom (y₀.hx i) ≫ f₀ ≫ eqToHom (z₀.hx i).symm).op ≫
        (𝓖 i).p.op.map (φ₀.component i).op = (𝓖 i).p.op.map (ψ₀.component i).op := by
      intro i
      have := φ₀.hcomponent i
      have := ψ₀.hcomponent i
      have h : (𝓖 i).p.map (φ₀.component i) ≫ eqToHom (y₀.hx i) ≫ f₀ ≫
          eqToHom (z₀.hx i).symm = (𝓖 i).p.map (ψ₀.component i) := by
        rw [IsHomLift.fac' (𝓖 i).p φ₀.hbase (φ₀.component i),
          IsHomLift.fac' (𝓖 i).p ψ₀.hbase (ψ₀.component i)]
        simp [← hbase]
      simpa only [Functor.op_map, Quiver.Hom.unop_op, CategoryTheory.op_comp] using
        congrArg Quiver.Hom.op h
    have hcomponent : ∀ i, ∃ χi : (y₀.x i) ⟶ (z₀.x i),
        ((𝓖 i).p.map χi = eqToHom (y₀.hx i) ≫ f₀ ≫ eqToHom (z₀.hx i).symm) ∧
          φ₀.component i ≫ χi = ψ₀.component i := by
      intro i
      obtain ⟨χi, hχi, -⟩ := (h𝓖 i).unique_lift
        (φ₀.component i).op (ψ₀.component i).op _ (hcommi i)
      exact ⟨χi.unop, Quiver.Hom.op_inj hχi.1, Quiver.Hom.op_inj hχi.2⟩
    choose χi hχi using hcomponent
    let χ₀ : y₀ ⟶ z₀ :=
      { hbase := f₀
        component := χi
        hcomponent := fun i ↦ by
          apply IsHomLift.of_fac' (𝓖 i).p f₀ (χi i) (y₀.hx i) (z₀.hx i)
          rw [(hχi i).1] }
    refine ⟨χ₀.op, ?_, ?_⟩
    · constructor
      · show (((PiOver.structureFunctor (fun i ↦ (𝓖 i).p)).map χ₀).op = f)
        exact Quiver.Hom.op_inj (by rfl)
      · exact Quiver.Hom.unop_inj (PiOver.Hom.ext' hbase fun i ↦ (hχi i).2)
    · intro χ' hχ'
      apply Quiver.Hom.unop_inj
      apply PiOver.Hom.ext'
      · simpa [PiOver.structureFunctor, χ₀, f₀] using congrArg Quiver.Hom.unop hχ'.1
      · intro i
        let fi : (𝓖 i).p.obj (y₀.x i) ⟶ (𝓖 i).p.obj (z₀.x i) :=
          eqToHom (y₀.hx i) ≫ f₀ ≫ eqToHom (z₀.hx i).symm
        let η : y₀ ⟶ z₀ := χ'.unop
        have hbase' : η.hbase = f₀ := by
          simpa [PiOver.structureFunctor, η, f₀] using congrArg Quiver.Hom.unop hχ'.1
        have hηmap : (𝓖 i).p.map (η.component i) = fi := by
          have hη := η.hcomponent i
          simpa [fi, η, hbase'] using IsHomLift.fac' (𝓖 i).p η.hbase (η.component i)
        have hcomp : φ₀ ≫ η = ψ₀ := by
          simpa [η, φ₀, ψ₀] using congrArg Quiver.Hom.unop hχ'.2
        have hηcomp : φ₀.component i ≫ η.component i = ψ₀.component i := by
          simpa [PiOver.comp_component] using
            congrArg (fun g : PiOver.Hom x₀ z₀ ↦ g.component i) hcomp
        obtain ⟨_, -, hu⟩ := (h𝓖 i).unique_lift
          (φ₀.component i).op (ψ₀.component i).op fi.op (hcommi i)
        have key : ∀ ζ : y₀.x i ⟶ z₀.x i, (𝓖 i).p.map ζ = fi →
            φ₀.component i ≫ ζ = ψ₀.component i → ζ.op = _ := fun ζ h₁ h₂ ↦
          hu ζ.op ⟨by
            simpa only [Functor.op_map, Quiver.Hom.unop_op] using congrArg Quiver.Hom.op h₁,
            by simpa only [CategoryTheory.op_comp] using congrArg Quiver.Hom.op h₂⟩
        exact Quiver.Hom.op_inj ((key _ hηmap hηcomp).trans (key _ (hχi i).1 (hχi i).2).symm)

end Deformation
