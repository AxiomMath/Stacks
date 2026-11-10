module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphisms
public import StacksFrontier.Deformation.Examples.Geometric.Schemes

/-!
# Forgetting the target of a deformation of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over the residue field `k`. A deformation of `f`
over an object of `𝒞_Λ` consists of flat families deforming `X` and `Y` together with a
morphism between them; keeping only the family that deforms `X` is a functor from the
deformation category of `f` to the deformation category of `X`. This file builds that
functor, checks that it is a morphism of categories over `𝒞_Λ`, and shows that it reflects
isomorphisms.

## Main definitions

* `Deformation.Examples.schemeMorphismSourceForgetful`: the functor from deformations of
  `f : X ⟶ Y` to deformations of `X` that keeps the source family and forgets the target
  family.

## Main results

* `Deformation.Examples.baseSpecMap_eq_residueSpecMap`: a morphism of `𝒞_Λ` into the residue
  field induces on spectra the closed-point map, because the residue field is terminal and
  its residue-field identification inverts the residue map.
* `Deformation.Examples.isIso_baseSpecMap`: taking spectra sends an isomorphism of `𝒞_Λ` to
  an isomorphism of schemes.
* `Deformation.Examples.SchemeMorphismFamily.isIso_of_isIso_base`: a morphism of flat families
  of scheme morphisms whose component on bases is invertible is itself invertible, both
  components being base changes of an isomorphism.
* `Deformation.Examples.schemeMorphismSourceForgetful_comp_projection`: the source-forgetful
  functor commutes with the two projections to `𝒞_Λ`, so it is a morphism of deformation
  categories.
* `Deformation.Examples.schemeMorphismSourceForgetful_reflectsIsomorphisms`: the
  source-forgetful functor reflects isomorphisms.

## Implementation notes

The identification of the fibre over the closed point carried by an object of
`Deformation.Examples.SchemeDeformationCategory` is a cartesian square over
`Deformation.Examples.residueSpecMap`, while the deformation category of a morphism records
that datum as an arrow to the special fibre in the category of flat families, hence over
`Deformation.Examples.baseSpecMap` of the arrow to the residue field. The two agree by
`Deformation.Examples.baseSpecMap_eq_residueSpecMap`, and the square the functor needs is the
vertical pasting of the source square of that arrow with its target square, rewritten along
the identity expressing that the family lies over its base.

Reflection of isomorphisms uses only that both pullback conditions on an arrow of families
are cartesian squares over the map of base spectra: an arrow whose base component is
invertible has both of its scheme components base changes of an isomorphism, hence
invertible, and the resulting inverse arrow satisfies the two cartesian conditions because a
commutative square two of whose parallel edges are isomorphisms is cartesian.

Tag 0E3X asserts more: when the canonical map `𝒪_Y ⟶ f_*𝒪_X` is invertible and `R¹f_*𝒪_X`
vanishes, the source-forgetful functor is an *equivalence*. That clause is not established
here; only the two clauses tagged below are.

The source reconstructs the target family `V` from a deformation `U` of `X` as the *ringed
space* `(Y, f_*𝒪_U)`, realized as a scheme by [Stacks, Tag 05YV]: `V` carries the same
underlying space as `Y`, with `Y ⟶ V` a thickening, and `𝒪_V = f_*𝒪_U` then supplies the
morphism `U ⟶ V`. Flatness of `𝒪_V` and the identification `𝒪_V / 𝔪 𝒪_V = 𝒪_Y` come from
filtering `𝒪_U` by the subsheaves `𝔪^i 𝒪_U`, whose graded pieces are `𝒪_X ⊗_k 𝔪^i/𝔪^{i+1}`
by flatness, so that `R¹f_*` kills each piece and the flatness criteria of
[Stacks, Tag 08LI] and [Stacks, Tag 063Y] can be read backwards by induction up the
filtration.

The target is emphatically *not* a relative spectrum of `f_*𝒪_U`: `V` and `Y` share an
underlying space, so there is no morphism `V ⟶ Y` for such a construction to be relative to.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.Examples

/-! ### Spectra of morphisms of the base category -/

section Base

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Taking spectra turns an isomorphism of `𝒞_Λ` into an isomorphism of schemes. -/
instance isIso_baseSpecMap {A B : ArtinianLocalAlgCat.{u, v, v} Λ k} (g : A ⟶ B) [IsIso g] :
    IsIso (baseSpecMap g) := by
  refine ⟨baseSpecMap (inv g), ?_, ?_⟩
  · rw [← baseSpecMap_comp, IsIso.inv_hom_id, baseSpecMap_id]
  · rw [← baseSpecMap_comp, IsIso.hom_inv_id, baseSpecMap_id]

end Base

/-- A morphism of `𝒞_Λ` from `A` to the residue field induces on spectra the closed-point
map of `A`: the residue-field identification of the residue field inverts its residue map,
so the underlying ring map of any such morphism is the residue map of `A`. -/
theorem baseSpecMap_eq_residueSpecMap {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (b : A ⟶ residueFieldBase Λ k) :
    baseSpecMap b = residueSpecMap A := by
  have hb : b.hom.toRingHom = Deformation.Artin.residueMap A := by
    ext a
    have h := b.residue_comm a
    rw [residueFieldBase_residueEquiv_residue] at h
    exact h
  change Spec.map (CommRingCat.ofHom b.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A))
  rw [hb]

/-! ### Arrows of flat families over an isomorphism of bases -/

namespace SchemeMorphismFamily

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An arrow of flat families of morphisms of schemes whose component on the bases is
invertible is itself invertible: its two scheme components are base changes of the
isomorphism of base spectra, hence isomorphisms, and the inverse triple satisfies the two
cartesian conditions. -/
theorem isIso_of_isIso_base {P Q : SchemeMorphismFamily.{u, v} Λ k} (ψ : P ⟶ Q)
    [IsIso ψ.base] : IsIso ψ := by
  have ht : IsIso ψ.target := ψ.target_pullback.isIso_fst_of_isIso
  have hs : IsIso ψ.source := ψ.source_pullback.flip.isIso_fst_of_isIso
  have hsq₁ : P.morphism ≫ inv ψ.target = inv ψ.source ≫ Q.morphism := by
    rw [IsIso.comp_inv_eq]
    calc
      P.morphism = (inv ψ.source ≫ ψ.source) ≫ P.morphism := by
        rw [IsIso.inv_hom_id, Category.id_comp]
      _ = inv ψ.source ≫ Q.morphism ≫ ψ.target := by
        rw [Category.assoc, ψ.source_pullback.w]
      _ = (inv ψ.source ≫ Q.morphism) ≫ ψ.target := (Category.assoc _ _ _).symm
  have hsq₂ : inv ψ.target ≫ Q.targetToBase =
      P.targetToBase ≫ baseSpecMap (inv ψ.base) := by
    rw [IsIso.inv_comp_eq]
    calc
      Q.targetToBase = Q.targetToBase ≫ baseSpecMap (inv ψ.base ≫ ψ.base) := by
        rw [IsIso.inv_hom_id, baseSpecMap_id, Category.comp_id]
      _ = (Q.targetToBase ≫ baseSpecMap ψ.base) ≫ baseSpecMap (inv ψ.base) := by
        rw [baseSpecMap_comp, Category.assoc]
      _ = (ψ.target ≫ P.targetToBase) ≫ baseSpecMap (inv ψ.base) := by
        rw [ψ.target_pullback.w]
      _ = ψ.target ≫ P.targetToBase ≫ baseSpecMap (inv ψ.base) := Category.assoc _ _ _
  refine ⟨⟨{ base := inv ψ.base
             source := inv ψ.source
             target := inv ψ.target
             source_pullback := IsPullback.of_vert_isIso ⟨hsq₁⟩
             target_pullback := IsPullback.of_horiz_isIso ⟨hsq₂⟩ }, ?_, ?_⟩⟩
  all_goals
    refine SchemeMorphismFamily.Hom.ext ?_ ?_ ?_ <;>
      first | exact IsIso.hom_inv_id _ | exact IsIso.inv_hom_id _

end SchemeMorphismFamily

/-! ### The source-forgetful functor -/

section SourceForgetful

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- The functor from deformations of a morphism `f : X ⟶ Y` of schemes over the residue
field to deformations of its source `X`, keeping the family that deforms `X` together with
its identification of the fibre over the closed point and forgetting the family that
deforms `Y`. -/
def schemeMorphismSourceForgetful :
    schemeMorphismDeformationCategory f pX pY hf ⥤
      SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX) where
  obj P :=
    { base := P.left.base
      scheme := P.left.source
      toBase := P.left.sourceToBase
      flat := P.left.source_flat
      specialMap := P.hom.source
      specialCartesian := by
        have h := P.hom.source_pullback.flip.paste_vert P.hom.target_pullback
        change IsPullback P.hom.source (f ≫ pY)
          (P.left.morphism ≫ P.left.targetToBase) (baseSpecMap P.hom.base) at h
        simpa [schemeMorphismFamilySpecialFiber, hf, P.left.over_base,
          baseSpecMap_eq_residueSpecMap] using h }
  map {P Q} h :=
    { base := h.left.base
      map := h.left.source
      cartesian := by
        have hh := h.left.source_pullback.flip.paste_vert h.left.target_pullback
        rw [P.left.over_base, Q.left.over_base] at hh
        exact hh
      special_compat := congrArg SchemeMorphismFamily.Hom.source (Over.w h) }
  map_id := by intro P; apply SchemeDeformationCategory.Hom.ext <;> rfl
  map_comp := fun {_ _ _} h g => by apply SchemeDeformationCategory.Hom.ext <;> rfl

/-- The base of the source deformation of `P` is the base of `P`. -/
@[simp]
theorem schemeMorphismSourceForgetful_obj_base
    (P : schemeMorphismDeformationCategory f pX pY hf) :
    ((schemeMorphismSourceForgetful f pX pY hf).obj P).base = P.left.base :=
  rfl

/-- The base component of the image of an arrow `h` of deformations of `f` is the base
component of `h`. -/
@[simp]
theorem schemeMorphismSourceForgetful_map_base
    {P Q : schemeMorphismDeformationCategory f pX pY hf} (h : P ⟶ Q) :
    ((schemeMorphismSourceForgetful f pX pY hf).map h).base = h.left.base :=
  rfl

/-- The source-forgetful functor commutes with the projections of the two deformation
categories to `𝒞_Λ`, so it is a morphism of categories over the base category: this is the
morphism of deformation categories `Def_{X ⟶ Y} ⟶ Def_X`. -/
@[stacks 0E3X "morphism of deformation categories"]
theorem schemeMorphismSourceForgetful_comp_projection :
    schemeMorphismSourceForgetful f pX pY hf ⋙
        schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX) =
      Over.forget (schemeMorphismFamilySpecialFiber f pX pY hf) ⋙
        schemeMorphismFamilyFunctor :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

/-- The source-forgetful functor reflects isomorphisms: an arrow of deformations of `f`
whose source component is invertible has invertible component on bases, and an arrow of
flat families over an isomorphism of bases is an isomorphism. -/
@[stacks 0E3X "reflects isomorphisms"]
instance schemeMorphismSourceForgetful_reflectsIsomorphisms :
    (schemeMorphismSourceForgetful f pX pY hf).ReflectsIsomorphisms where
  reflects {P Q} h _ := by
    have hbase : IsIso h.left.base := by
      rw [← schemeMorphismSourceForgetful_map_base f pX pY hf h]
      exact (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
        (Over.mk pX)).map_isIso ((schemeMorphismSourceForgetful f pX pY hf).map h)
    have hleft : IsIso h.left := SchemeMorphismFamily.isIso_of_isIso_base h.left
    have hmap : IsIso ((Over.forget
      (schemeMorphismFamilySpecialFiber f pX pY hf)).map h) := hleft
    exact isIso_of_reflects_iso h (Over.forget _)

end SourceForgetful

end Deformation.Examples

end
