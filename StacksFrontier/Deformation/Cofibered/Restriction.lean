module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Cofibered

/-!
# Restricting the base of a category cofibered in groupoids

Remark (15) of Stacks 06GK. Let `p : F ⥤ C` be a category cofibered in groupoids and let `C'` be a
full subcategory of `C`, cut out by an object property `P`. The restriction `F|_{C'}` is the full
subcategory of `F` whose objects lie over objects of `C'`, and `p` restricts to a functor
`p|_{C'} : F|_{C'} ⥤ C'`, which is again cofibered in groupoids.

## Main definitions

* `Deformation.restrictBase`: the restricted functor `p|_{C'} : F|_{C'} ⥤ C'`, where `F|_{C'}` is
  the full subcategory `(P.inverseImage p).FullSubcategory`.

## Main results

* `Deformation.isCofiberedInGroupoids_mk`: the defining conditions of a category cofibered in
  groupoids, stated in `F` and `C` rather than in their opposites, imply that `p` is cofibered in
  groupoids.
* `Deformation.existsUnique_of_isCofiberedInGroupoids`: conversely, the unique factorisation
  condition in `F` and `C`.
* `Deformation.isCofiberedInGroupoids_restrictBase`: the restriction is cofibered in groupoids.

## References

* [Stacks Project, Tag 06GK](https://stacks.math.columbia.edu/tag/06GK)
* [Stacks Project, Tag 06GR](https://stacks.math.columbia.edu/tag/06GR)
-/

@[expose] public section

namespace Deformation

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]

/-- The two conditions of Stacks 06GJ, read in `F` and `C`: every `f : U ⟶ V` has a lift with any
prescribed source over `U`, and for `a : x ⟶ y`, `b : x ⟶ z` and `f : p y ⟶ p z` with
`p a ≫ f = p b` there is a unique `c : y ⟶ z` over `f` with `a ≫ c = b`. They make `p` cofibered
in groupoids. -/
theorem isCofiberedInGroupoids_mk {p : F ⥤ C}
    (h₁ : ∀ {U V : C} (f : U ⟶ V) (x : F), p.obj x = U → ∃ (y : F) (φ : x ⟶ y), p.IsHomLift f φ)
    (h₂ : ∀ {x y z : F} (a : x ⟶ y) (b : x ⟶ z) (f : p.obj y ⟶ p.obj z),
      p.map a ≫ f = p.map b → ∃! c : y ⟶ z, p.map c = f ∧ a ≫ c = b) :
    IsCofiberedInGroupoids p := by
  refine ⟨fun {V U} f x hx ↦ ?_, fun {x y z} φ ψ f hf ↦ ?_⟩
  · obtain ⟨y, φ, hφ⟩ := h₁ f.unop x.unop (congrArg Opposite.unop hx)
    exact ⟨Opposite.op y, φ.op, isHomLift_op p f.unop φ⟩
  · obtain ⟨c, ⟨hc, hca⟩, huniq⟩ :=
      h₂ φ.unop ψ.unop f.unop (congrArg Quiver.Hom.unop hf)
    refine ⟨c.op, ⟨congrArg Quiver.Hom.op hc, congrArg Quiver.Hom.op hca⟩, fun χ hχ ↦ ?_⟩
    exact congrArg Quiver.Hom.op
      (huniq χ.unop ⟨congrArg Quiver.Hom.unop hχ.1, congrArg Quiver.Hom.unop hχ.2⟩)

/-- The unique factorisation condition of a category cofibered in groupoids, read in `F` and
`C`. -/
theorem existsUnique_of_isCofiberedInGroupoids {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {x y z : F} (a : x ⟶ y) (b : x ⟶ z) (f : p.obj y ⟶ p.obj z) (h : p.map a ≫ f = p.map b) :
    ∃! c : y ⟶ z, p.map c = f ∧ a ≫ c = b := by
  obtain ⟨c, ⟨hc, hca⟩, huniq⟩ :=
    hp.unique_lift a.op b.op f.op (congrArg Quiver.Hom.op h)
  refine ⟨c.unop, ⟨congrArg Quiver.Hom.unop hc, congrArg Quiver.Hom.unop hca⟩, fun χ hχ ↦ ?_⟩
  exact congrArg Quiver.Hom.unop
    (huniq χ.op ⟨congrArg Quiver.Hom.op hχ.1, congrArg Quiver.Hom.op hχ.2⟩)

variable (P : ObjectProperty C) (p : F ⥤ C)

/-- **Stacks 06GK (15).** The restriction `p|_{C'} : F|_{C'} ⥤ C'` of `p : F ⥤ C` to the full
subcategory `C'` of `C` cut out by `P`: here `F|_{C'}` is the full subcategory of `F` on the objects
lying over objects of `C'`, and the functor is `p` on objects and morphisms. -/
@[stacks 06GK "(15) the restriction F|_{C'} → C' to a full subcategory C' of the base"]
def restrictBase : (P.inverseImage p).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((P.inverseImage p).ι ⋙ p) (fun x ↦ x.2)

/-- The restriction followed by the inclusion of `C'` is `p` restricted to `F|_{C'}`. -/
theorem restrictBase_comp_ι : restrictBase P p ⋙ P.ι = (P.inverseImage p).ι ⋙ p :=
  rfl

/-- **Stacks 06GK (15).** The restriction of a category cofibered in groupoids to a full
subcategory of its base is cofibered in groupoids. -/
@[stacks 06GK "(15) the restriction F|_{C'} → C' is cofibered in groupoids"]
theorem isCofiberedInGroupoids_restrictBase {P : ObjectProperty C} {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) : IsCofiberedInGroupoids (restrictBase P p) := by
  apply isCofiberedInGroupoids_mk
  · intro U V f x hx
    have hx' : p.obj x.obj = U.obj := congrArg ObjectProperty.FullSubcategory.obj hx
    obtain ⟨y, φ, hφ⟩ := exists_pushforward hp f.hom x.obj hx'
    have hy : p.obj y = V.obj := IsHomLift.codomain_eq p f.hom φ
    let y' : (P.inverseImage p).FullSubcategory := ⟨y, by
      change P (p.obj y)
      rw [hy]
      exact V.2⟩
    let φ' : x ⟶ y' := ObjectProperty.homMk φ
    have hcod : (restrictBase P p).obj y' = V := ObjectProperty.FullSubcategory.ext hy
    refine ⟨y', φ', IsHomLift.of_fac' _ f φ' hx hcod ?_⟩
    apply P.ι.map_injective
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    exact IsHomLift.fac' p f.hom φ
  · intro x y z a b f h
    have h' : p.map a.hom ≫ f.hom = p.map b.hom := congrArg (fun g ↦ P.ι.map g) h
    obtain ⟨c, ⟨hc, hca⟩, huniq⟩ :=
      existsUnique_of_isCofiberedInGroupoids hp a.hom b.hom f.hom h'
    refine ⟨ObjectProperty.homMk c, ⟨ObjectProperty.hom_ext _ hc,
      ObjectProperty.hom_ext _ hca⟩, fun χ hχ ↦ ?_⟩
    exact ObjectProperty.hom_ext _
      (huniq χ.hom ⟨congrArg (fun g ↦ P.ι.map g) hχ.1, congrArg (fun g ↦ g.hom) hχ.2⟩)

end Deformation
