module

public import StacksFrontier.Deformation.Examples.Geometric.Base
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSource
public import StacksFrontier.Deformation.Examples.Geometric.SchemesRimSchlessingerSquares
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport
public import StacksFrontier.Deformation.Terminal
import StacksFrontier.Deformation.Artin.Predeformation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The deformation category of a fixed scheme over the residue field

A deformation of a fixed scheme `X` over `k` (`Deformation.Examples.SchemeDeformationCategory`)
is a flat family carrying a cartesian square that identifies the fibre over the closed point with
`X`. This file identifies the category of deformations of `X` with the category of flat families
lying over `X`, viewed as a flat family over the residue-field object of `𝒞_Λ`, and deduces that
the deformation category of a fixed scheme over `k` is a deformation category.

## Main definitions

* `Deformation.Examples.flatSchemeFamilySpecialFiber`: a scheme over `k` as a flat family over
  the residue-field object of `𝒞_Λ`.
* `Deformation.Examples.schemeDeformationToOver`: the comparison functor from the deformation
  category of `X` to the category of flat families over that trivial family.

## Main results

* `Deformation.Examples.baseSpecMap_from_residueFieldBase`: the terminal arrow of `𝒞_Λ` induces
  the closed point on spectra.
* `Deformation.Examples.isDeformationCategory_schemeDeformationCategoryProjection`: the
  deformation category of a fixed scheme over `k` is a deformation category.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DY8](https://stacks.math.columbia.edu/tag/0DY8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The terminal arrow induces the closed point -/

/-- The residue map of `residueFieldBase` is the identity: its carrier is `k` itself and its
residue identification is inverse to the residue map. -/
theorem residueMap_residueFieldBase :
    Deformation.Artin.residueMap (residueFieldBase.{u, u} Λ k) = RingHom.id k := by
  ext a
  exact residueFieldBase_residueEquiv_residue Λ k a

/-- The unique arrow of `𝒞_Λ` from `A` to the residue field is the residue map of `A`. -/
theorem hom_from_residueFieldBase (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).from A).hom.toRingHom =
      Deformation.Artin.residueMap A := by
  have h := Deformation.Artin.residueMap_comp
    ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).from A)
  rw [residueMap_residueFieldBase] at h
  simpa using h

/-- **The terminal arrow of `𝒞_Λ` induces the closed point on spectra.** The map of spectra
induced by the unique arrow from `A` to the residue field is the inclusion of the closed point. -/
theorem baseSpecMap_from_residueFieldBase (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    baseSpecMap ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).from A) = residueSpecMap A := by
  exact baseSpecMap_eq_residueSpecMap _ _

/-! ### A scheme over the residue field as a flat family -/

/-- A scheme over `k`, viewed as a flat family over the residue-field object of `𝒞_Λ`. -/
def flatSchemeFamilySpecialFiber (X : Over (Spec (.of k))) :
    FlatSchemeFamily.{u, u, u} Λ k where
  base := residueFieldBase Λ k
  scheme := X.left
  toBase := X.hom
  flat := by
    have : Subsingleton (baseSpec (residueFieldBase Λ k)) := by
      change Subsingleton (Spec (.of k))
      infer_instance
    have : IsIntegral (baseSpec (residueFieldBase Λ k)) := by
      change IsIntegral (Spec (.of k))
      infer_instance
    infer_instance

/-- The base of `flatSchemeFamilySpecialFiber X` is the residue-field object of `𝒞_Λ`. -/
@[simp]
theorem flatSchemeFamilySpecialFiber_base (X : Over (Spec (.of k))) :
    (flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X).base = residueFieldBase Λ k := rfl

/-- The total space of `flatSchemeFamilySpecialFiber X` is the underlying scheme of `X`. -/
@[simp]
theorem flatSchemeFamilySpecialFiber_scheme (X : Over (Spec (.of k))) :
    (flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X).scheme = X.left := rfl

/-- The structure morphism of `flatSchemeFamilySpecialFiber X` is the structure morphism of
`X`. -/
@[simp]
theorem flatSchemeFamilySpecialFiber_toBase (X : Over (Spec (.of k))) :
    (flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X).toBase = X.hom := rfl

/-! ### The deformation category of `X` as a category of objects over the trivial family -/

/-- The underlying flat family of a deformation of `X`: forget the identification of the fibre
over the closed point. -/
def SchemeDeformationCategory.toFamily {X : Over (Spec (.of k))}
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) : FlatSchemeFamily.{u, u, u} Λ k where
  base := P.base
  scheme := P.scheme
  toBase := P.toBase
  flat := P.flat

/-- The identification of the fibre over the closed point, read as a cartesian square over the
map of spectra induced by the terminal arrow of `𝒞_Λ`. -/
theorem SchemeDeformationCategory.specialCartesian_from {X : Over (Spec (.of k))}
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    IsPullback P.specialMap X.hom P.toBase
      (baseSpecMap ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).from P.base)) := by
  rw [baseSpecMap_eq_residueSpecMap]
  exact P.specialCartesian

/-- The base-change arrow from the underlying family of a deformation of `X` to the trivial
family on `X`: its base component is the terminal arrow and its cartesian square is the
identification of the fibre over the closed point. -/
def SchemeDeformationCategory.toSpecialFiber {X : Over (Spec (.of k))}
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    P.toFamily ⟶ flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X where
  base := (isTerminal_residueFieldBase (Λ := Λ) (k := k)).from P.base
  map := P.specialMap
  cartesian := P.specialCartesian_from

/-- **The deformation category of `X` sits over the trivial family on `X`.**  A deformation of
`X` is its underlying flat family together with the base-change arrow to the trivial family on
`X`; a morphism of deformations is the underlying morphism of families, and its compatibility
with the two identifications of the fibre over the closed point is exactly the triangle over
the trivial family. -/
def schemeDeformationToOver (X : Over (Spec (.of k))) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X ⥤
      Over (flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X) where
  obj P := Over.mk P.toSpecialFiber
  map {P Q} f := Over.homMk
    (U := Over.mk P.toSpecialFiber) (V := Over.mk Q.toSpecialFiber)
    { base := f.base
      map := f.map
      cartesian := f.cartesian }
    (FlatSchemeFamily.Hom.ext ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).hom_ext _ _)
      f.special_compat)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The flat family underlying the image of a deformation `P` under `schemeDeformationToOver X`
is the underlying flat family of `P`. -/
@[simp]
theorem schemeDeformationToOver_obj_left {X : Over (Spec (.of k))}
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    ((schemeDeformationToOver.{u} (Λ := Λ) (k := k) X).obj P).left = P.toFamily := rfl

/-- The comparison functor `schemeDeformationToOver X` is faithful. -/
instance schemeDeformationToOver_faithful (X : Over (Spec (.of k))) :
    (schemeDeformationToOver.{u} (Λ := Λ) (k := k) X).Faithful where
  map_injective {P Q} f g h := by
    have h' : (⟨f.base, f.map, f.cartesian⟩ : P.toFamily ⟶ Q.toFamily) =
        ⟨g.base, g.map, g.cartesian⟩ := congrArg (fun m => m.left) h
    exact SchemeDeformationCategory.Hom.ext (congrArg FlatSchemeFamily.Hom.base h')
      (congrArg FlatSchemeFamily.Hom.map h')

/-- The comparison functor `schemeDeformationToOver X` is full. -/
instance schemeDeformationToOver_full (X : Over (Spec (.of k))) :
    (schemeDeformationToOver.{u} (Λ := Λ) (k := k) X).Full where
  map_surjective f :=
    ⟨{ base := f.left.base
       map := f.left.map
       cartesian := f.left.cartesian
       special_compat := congrArg FlatSchemeFamily.Hom.map (Over.w f) },
      rfl⟩

/-- **A base-change arrow to the trivial family on `X` is an identification of the fibre over
the closed point.** For `φ : Q ⟶ flatSchemeFamilySpecialFiber X`, the square formed by `φ.map`,
the structure morphisms and the closed point of the base of `Q` is cartesian. -/
theorem isPullback_map_of_hom_flatSchemeFamilySpecialFiber {X : Over (Spec (.of k))}
    {Q : FlatSchemeFamily.{u, u, u} Λ k}
    (φ : Q ⟶ flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X) :
    IsPullback φ.map X.hom Q.toBase (residueSpecMap Q.base) := by
  rw [← baseSpecMap_eq_residueSpecMap _ φ.base]
  exact φ.cartesian

/-- The comparison functor `schemeDeformationToOver X` is surjective on objects: every flat
family over the trivial family on `X` comes from a deformation of `X`. -/
theorem schemeDeformationToOver_obj_surjective (X : Over (Spec (.of k))) :
    Function.Surjective (schemeDeformationToOver.{u} (Λ := Λ) (k := k) X).obj := by
  intro Y
  refine ⟨{ base := Y.left.base
            scheme := Y.left.scheme
            toBase := Y.left.toBase
            flat := Y.left.flat
            specialMap := Y.hom.map
            specialCartesian := isPullback_map_of_hom_flatSchemeFamilySpecialFiber Y.hom }, ?_⟩
  exact congrArg Over.mk <| FlatSchemeFamily.Hom.ext
    ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).hom_ext _ _).symm rfl

/-- The comparison functor `schemeDeformationToOver X` commutes with the projections to
`𝒞_Λ`. -/
theorem schemeDeformationToOver_comp_objectsOverFunctor (X : Over (Spec (.of k))) :
    schemeDeformationToOver.{u} (Λ := Λ) (k := k) X ⋙
        objectsOverFunctor (flatSchemeFamilyProjection.{u, u, u} (Λ := Λ) (k := k))
          (flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X) =
      schemeDeformationCategoryProjection.{u} (Λ := Λ) (k := k) X := rfl

/-! ### The deformation category of a fixed scheme -/

/-- The category of flat families lying over the trivial family on `X` is a deformation
category. -/
theorem isDeformationCategory_objectsOverFunctor_flatSchemeFamilySpecialFiber
    (X : Over (Spec (.of k))) :
    IsDeformationCategory.{u, u, u}
      (objectsOverFunctor (flatSchemeFamilyProjection.{u, u, u} (Λ := Λ) (k := k))
        (flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X)) := by
  have hRS : SatisfiesRS (flatSchemeFamilyProjection.{u, u, u} (Λ := Λ) (k := k)) :=
    satisfiesRS_flatSchemeFamilyProjection.{u, u, u}
  let p := flatSchemeFamilyProjection.{u, u, u} (Λ := Λ) (k := k)
  let x := flatSchemeFamilySpecialFiber.{u} (Λ := Λ) (k := k) X
  have ht : IsTerminal (p.obj x) := isTerminal_residueFieldBase
  have hs : IsTerminal (residueFieldObject.{u, u, u} Λ k) :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot _
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{u} k))
  refine ⟨⟨isCofiberedInGroupoids_overForget hRS.1 x ht, ?_⟩, ?_⟩
  · exact objectsOverFunctor_fiber_equiv_punit_of_isTerminal p hRS.1 x ht _ hs
  · exact satisfiesRS_objectsOverFunctor_of_isTerminal p hRS x ht

/-- The deformation category of a fixed scheme `X` over the residue field is a deformation
category: a predeformation category satisfying (RS). -/
@[stacks 0DY8 "the clause that the deformation category of a fixed scheme over k is a \
deformation category, unconditionally; condition (RS) for the category of all flat scheme \
families of Example 0DY7 is Deformation.Examples.satisfiesRS_flatSchemeFamilyProjection",
  sga "7 VI 1.1(c)" "more general"]
theorem isDeformationCategory_schemeDeformationCategoryProjection
    (X : Over (Spec (.of k))) :
    IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection.{u} (Λ := Λ) (k := k) X) := by
  rw [← schemeDeformationToOver_comp_objectsOverFunctor]
  exact isDeformationCategory_comp _ (schemeDeformationToOver_obj_surjective X) _
    (isDeformationCategory_objectsOverFunctor_flatSchemeFamilySpecialFiber X)

end Deformation.Examples

end
