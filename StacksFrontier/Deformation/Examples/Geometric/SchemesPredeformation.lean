module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.Deformation.Examples.Geometric.SchemesCofibered
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Terminal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The deformation category of a scheme is a predeformation category

Let `k` be a field and `X` a scheme over `k`. The category of flat deformations of `X` over the
objects of `𝒞_Λ` of [Stacks Project, Tag 0DY7] is cofibered in groupoids
(`Deformation.Examples.schemeDeformationCategoryProjection_cofiberedInGroupoids`); this file
supplies the other half of the predeformation condition of [Stacks Project, Tag 06GC], that the
fibre over the residue field is equivalent to the category with one object and one morphism.

The content is that the residue point `Spec k ⟶ Spec A` is an isomorphism when the maximal ideal
of `A` vanishes, which is the case for the residue-field object: the residue map of such an `A` is
bijective, being the composite of the quotient by the zero ideal with the chosen identification of
the residue field with `k`. For a deformation `P` whose base is the residue-field object, the
cartesian square `Deformation.Examples.SchemeDeformationCategory.specialCartesian` then has an
invertible right-hand arrow, so its left-hand arrow `P.specialMap : X ⟶ P.scheme` is invertible
too. Two consequences:

* the arrows of the fibre are unique, since `P.specialMap ≫ map = Q.specialMap` determines `map`
  once `P.specialMap` is epi, and the base component is pinned by the lifting condition; and
* `X` itself is an object of the fibre, flat over `Spec` of the residue-field object because every
  morphism to the spectrum of a field is flat and the residue point is invertible.

A nonempty category all of whose hom-sets are singletons is equivalent to the one-object category,
which is the predeformation condition.

## Main definitions

* `Deformation.Examples.residueTrivialDeformation`: `X` itself, read as a deformation over the
  residue-field object.
* `Deformation.Examples.residueFiberHom`: the canonical arrow between two deformations in the
  fibre over the residue field.
* `Deformation.Examples.residueFiberEquivPUnit`: the fibre over the residue field is the
  one-object category.

## Main results

* `Deformation.Examples.isIso_residueSpecMap_of_maximalIdeal_eq_bot`: the residue point of an
  object of `𝒞_Λ` with vanishing maximal ideal is an isomorphism of schemes.
* `Deformation.Examples.isIso_specialMap_of_base_eq_residueFieldObject`: the special-fibre
  immersion of a deformation over the residue-field object is an isomorphism.
* `Deformation.Examples.residueFiberHom_subsingleton`: arrows of that fibre are unique.
* `Deformation.Examples.schemeDeformationCategoryProjection_isPredeformationCategory`: the
  deformation category of a scheme is a predeformation category.

## Implementation notes

Flatness of the structure morphism of `Deformation.Examples.residueTrivialDeformation` is not
proved stalkwise on `Spec` of the residue-field object, whose carrier is the universe lift
`ULift k`: a `Field` instance on that carrier is not found by synthesis, and supplying one
locally installs a second `CommRing` structure, which is the pitfall recorded in
`StacksFrontier/Deformation/Examples/Geometric/Base.lean`. Instead flatness is read on
`Spec (CommRingCat.of k)`, where `k` carries its own `Field` instance, and transported along the
residue point, which is invertible; `Flat` is stable under composition and contains the
isomorphisms, so instance search closes the goal.

`Deformation.Examples.residueFiberHom_subsingleton` is proved in term mode rather than by
rewriting. The goals produced by `CategoryTheory.Functor.Fiber.hom_ext` are stated through
`CategoryTheory.Functor.Fiber.fiberInclusion`, which is definitionally but not reducibly the
first projection of the fibre subtype, so `rw` refuses the motive while `exact` crosses the
identification. This is the escape hatch documented for fibre spellings elsewhere in the
library.

No `@[stacks]` attribute is carried here. The predeformation condition is one half of the
assertion of [Stacks Project, Tag 0DY8] that Example 0DY7 is a deformation category, whose other
half is the Rim–Schlessinger condition; the attribute belongs on a declaration stating the whole
of a clause, and the consumer of this file is the infinitesimal-automorphism clause of
[Stacks Project, Tag 0DY9], which carries its own.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The residue point of an object with vanishing maximal ideal -/

/-- **The residue map of an object of `𝒞_Λ` with vanishing maximal ideal is bijective.** It is
the quotient by the maximal ideal followed by the chosen identification of the residue field
with `k`; the first is bijective because the ideal is zero, and the second is an algebra
isomorphism. -/
theorem residueMap_bijective_of_maximalIdeal_eq_bot (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : IsLocalRing.maximalIdeal (A : Type u) = ⊥) :
    Function.Bijective (Deformation.Artin.residueMap A) :=
  A.residueEquiv.bijective.comp
    ⟨ArtinianLocalAlgCat.residue_injective_of_maximalIdeal_eq_bot A hA,
      Ideal.Quotient.mk_surjective⟩

/-- **The residue point of an object of `𝒞_Λ` with vanishing maximal ideal is an isomorphism of
schemes**, being the spectrum of a bijective ring homomorphism. -/
theorem isIso_residueSpecMap_of_maximalIdeal_eq_bot (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : IsLocalRing.maximalIdeal (A : Type u) = ⊥) :
    IsIso (residueSpecMap A) := by
  have : IsIso (CommRingCat.ofHom (Deformation.Artin.residueMap A)) :=
    (RingEquiv.toCommRingCatIso
      (RingEquiv.ofBijective _ (residueMap_bijective_of_maximalIdeal_eq_bot A hA))).isIso_hom
  exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom
    (Deformation.Artin.residueMap A))))

/-- The maximal ideal of the residue-field object vanishes: its carrier is the universe lift of
the field `k`. -/
theorem maximalIdeal_residueFieldObject_eq_bot :
    IsLocalRing.maximalIdeal (residueFieldObject.{u, u, u} Λ k : Type u) = ⊥ :=
  IsLocalRing.maximalIdeal_eq_bot (R := ULift.{u} k)

/-- The residue point of the residue-field object is an isomorphism of schemes. -/
theorem isIso_residueSpecMap_residueFieldObject :
    IsIso (residueSpecMap (residueFieldObject.{u, u, u} Λ k)) :=
  isIso_residueSpecMap_of_maximalIdeal_eq_bot _ maximalIdeal_residueFieldObject_eq_bot

/-- `baseSpecMap` of an identification of objects of `𝒞_Λ` is an isomorphism. -/
theorem isIso_baseSpecMap_eqToHom {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = B) :
    IsIso (baseSpecMap (eqToHom h)) := by
  subst h
  rw [eqToHom_refl, baseSpecMap_id]
  infer_instance

/-! ### Deformations over the residue-field object -/

section

variable {X : Over (Spec (CommRingCat.of k))}

/-- **The special-fibre immersion of a deformation over the residue-field object is an
isomorphism.** The cartesian square identifying the fibre over the closed point has the residue
point as its right-hand arrow, and that is invertible. -/
theorem isIso_specialMap_of_base_eq_residueFieldObject
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (hP : P.base = residueFieldObject.{u, u, u} Λ k) : IsIso P.specialMap := by
  have : IsIso (residueSpecMap P.base) := by
    rw [hP]
    exact isIso_residueSpecMap_residueFieldObject
  exact P.specialCartesian.isIso_fst_of_isIso

/-- The structure morphism of `Deformation.Examples.residueTrivialDeformation` is flat: it is the
structure morphism of `X` over `Spec k`, which is flat because the local rings of the spectrum of
a field are fields, followed by the invertible residue point. -/
theorem flat_toBase_residueTrivialDeformation :
    Flat (X.hom ≫ residueSpecMap (residueFieldObject.{u, u, u} Λ k)) := by
  have : Flat X.hom :=
    flat_of_isField_stalk X.hom fun _ => isField_stalk_Spec_field k _
  have := isIso_residueSpecMap_residueFieldObject (Λ := Λ) (k := k)
  infer_instance

/-- **`X` itself, read as a deformation over the residue-field object.** Its total space is `X`,
its structure morphism is the structure morphism of `X` followed by the residue point, and its
special-fibre immersion is the identity; the identification of the fibre over the closed point is
cartesian because the residue point is invertible. -/
def residueTrivialDeformation (X : Over (Spec (CommRingCat.of k))) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X where
  base := residueFieldObject.{u, u, u} Λ k
  scheme := X.left
  toBase := X.hom ≫ residueSpecMap (residueFieldObject.{u, u, u} Λ k)
  flat := flat_toBase_residueTrivialDeformation
  specialMap := 𝟙 X.left
  specialCartesian := by
    have := isIso_residueSpecMap_residueFieldObject (Λ := Λ) (k := k)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩

end

/-- `X` itself, read as an object of the fibre of the projection over the residue-field
object. -/
abbrev residueTrivialFiberObj (X : Over (Spec (CommRingCat.of k))) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k) :=
  ⟨residueTrivialDeformation X, rfl⟩

/-! ### The fibre over the residue field is a point -/

section Fibre

variable {X : Over (Spec (CommRingCat.of k))}

/-- **The canonical arrow between two deformations in the fibre over the residue field.** Both
special-fibre immersions are invertible, so the compatibility condition
`Q.specialMap ≫ map = P.specialMap` leaves exactly one candidate for the component on total
spaces; the base component is the identification of the two base objects, and the square is
cartesian because both of its horizontal arrows are invertible. -/
def residueFiberHomVal
    (x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)) : x.1 ⟶ y.1 := by
  haveI hx : IsIso x.1.specialMap := isIso_specialMap_of_base_eq_residueFieldObject x.1 x.2
  haveI hy : IsIso y.1.specialMap := isIso_specialMap_of_base_eq_residueFieldObject y.1 y.2
  refine
    { base := eqToHom (x.2.trans y.2.symm)
      map := inv y.1.specialMap ≫ x.1.specialMap
      cartesian := ?_
      special_compat := by simp }
  have := isIso_baseSpecMap_eqToHom (x.2.trans y.2.symm)
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  refine (cancel_epi y.1.specialMap).mp ?_
  calc y.1.specialMap ≫ (inv y.1.specialMap ≫ x.1.specialMap) ≫ x.1.toBase
      = x.1.specialMap ≫ x.1.toBase := by simp
    _ = X.hom ≫ residueSpecMap x.1.base := x.1.specialCartesian.w
    _ = X.hom ≫ residueSpecMap y.1.base ≫ baseSpecMap (eqToHom (x.2.trans y.2.symm)) := by
        rw [residueSpecMap_naturality]
    _ = y.1.specialMap ≫ y.1.toBase ≫ baseSpecMap (eqToHom (x.2.trans y.2.symm)) := by
        rw [← Category.assoc, ← Category.assoc, y.1.specialCartesian.w]

/-- The canonical arrow lies over the identity of the residue-field object, its base component
being the identification of the two base objects. -/
theorem residueFiberHom_isHomLift
    (x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift
      (𝟙 (residueFieldObject.{u, u, u} Λ k)) (residueFiberHomVal x y) := by
  refine IsHomLift.of_fac' _ (𝟙 (residueFieldObject.{u, u, u} Λ k))
    (residueFiberHomVal x y) x.2 y.2 ?_
  show eqToHom (x.2.trans y.2.symm) = _
  simp

/-- The canonical arrow of the fibre over the residue field. -/
def residueFiberHom
    (x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)) : x ⟶ y :=
  ⟨residueFiberHomVal x y, residueFiberHom_isHomLift x y⟩

/-- **Arrows of the fibre over the residue field are unique.** The component on total spaces is
determined by the compatibility with the special-fibre immersions, which are invertible hence
epi, and the base component is determined by the lifting condition. -/
instance residueFiberHom_subsingleton
    (x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)) : Subsingleton (x ⟶ y) := by
  have hy : IsIso y.1.specialMap := isIso_specialMap_of_base_eq_residueFieldObject y.1 y.2
  refine ⟨fun f g => ?_⟩
  apply Functor.Fiber.hom_ext
  apply SchemeDeformationCategory.Hom.ext
  · have := f.2
    have := g.2
    exact (IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
      (𝟙 (residueFieldObject.{u, u, u} Λ k)) f.val).trans
      (IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
        (𝟙 (residueFieldObject.{u, u, u} Λ k)) g.val).symm
  · exact (cancel_epi y.1.specialMap).mp
      (f.val.special_compat.trans g.val.special_compat.symm)

/-- Every arrow of the fibre over the residue field is invertible: the two composites are arrows
of the fibre, hence are the identities by uniqueness. -/
def residueFiberIso
    (x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)) : x ≅ y where
  hom := residueFiberHom x y
  inv := residueFiberHom y x
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- **The fibre over the residue field is the category with one object and one morphism.** It is
nonempty, containing `X` itself as `Deformation.Examples.residueTrivialDeformation`, and all of
its arrows are unique and invertible, so the constant functors in the two directions are mutually
inverse. -/
def residueFiberEquivPUnit (X : Over (Spec (CommRingCat.of k))) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
        (residueFieldObject.{u, u, u} Λ k) ≌ Discrete PUnit.{u + 2} :=
  CategoryTheory.Equivalence.mk
    ((Functor.const _).obj (Discrete.mk PUnit.unit))
    ((Functor.const _).obj (residueTrivialFiberObj X))
    (NatIso.ofComponents (fun x => residueFiberIso x (residueTrivialFiberObj X))
      fun _ => Subsingleton.elim _ _)
    (Discrete.natIso fun _ => eqToIso (congrArg Discrete.mk (Subsingleton.elim _ _)))

end Fibre

/-- **The deformation category of a scheme over `k` is a predeformation category.** It is
cofibered in groupoids by
`Deformation.Examples.schemeDeformationCategoryProjection_cofiberedInGroupoids`, and its fibre
over the residue field is the one-object category by
`Deformation.Examples.residueFiberEquivPUnit`. -/
@[sga "7 VI 1.1(c)" "more general"]
theorem schemeDeformationCategoryProjection_isPredeformationCategory
    (X : Over (Spec (CommRingCat.of k))) :
    IsPredeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) where
  cofibered := schemeDeformationCategoryProjection_cofiberedInGroupoids X
  specialFiber := ⟨residueFiberEquivPUnit X⟩

end Deformation.Examples

end
