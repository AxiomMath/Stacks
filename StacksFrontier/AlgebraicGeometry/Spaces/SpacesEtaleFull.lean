module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSectionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleFaithful

/-!
# Fullness of base change on the spaces-étale sites of a universal homeomorphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is integral,
universally injective and surjective. Base change `V ↦ V_X = X ×_Y V` is then a fully faithful
functor from the spaces-étale site of `Y` to that of `X`.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_projection`: the
  projection `V'_X ⟶ V'` of a base-change datum along `f` is integral, universally injective and
  surjective.
* `AlgebraicGeometry.Space.existsUnique_hom_of_spacesBaseChange_of_isIntegralHom`: a morphism
  from a base change `V'_X` to an object `V` of the spaces-étale site of `Y`, compatible with
  the structure morphisms, extends uniquely across the projection `V'_X ⟶ V'`.
* `AlgebraicGeometry.Space.full_spacesBaseChange_of_isIntegralHom_of_universallyInjective`: the
  base-change functor is full.
* `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsIntegralHomOfUniversallyInjective`:
  the base-change functor is fully faithful.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The projection of a base-change datum -/

/-- The projection `V'_X ⟶ V'` of a base-change datum along `f` is integral, universally injective
and surjective if `f` is. -/
theorem isIntegralHom_universallyInjective_isSurjective_projection (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (D : SpacesBaseChange B S hS f)
    (V' : SpacesEtale B S hS Y) :
    IsIntegralHom B S hS (D.projection.app V').hom ∧
      UniversallyInjective B S hS (D.projection.app V').hom ∧
      IsSurjective B S hS (D.projection.app V').hom :=
  have sq := AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V')
  ⟨isIntegralHom_of_isPullback B S hS sq.flip hint,
    universallyInjective_of_isPullback B S hS X.property V'.1.left.property Y.property f.hom
      V'.1.hom.hom hui sq,
    isSurjective_of_isPullback B S hS (D.isPullback V').flip hsurj⟩

/-! ### Descending a morphism across the projection -/

/-- Let `f : X ⟶ Y` be integral, universally injective and surjective, let `V', V` be objects of
the spaces-étale site of `Y`, and let `d : V'_X ⟶ V` be a morphism of algebraic spaces whose
composite with the structure morphism of `V` is the projection followed by that of `V'`. Then
`d` extends uniquely to a morphism `V' ⟶ V` over `Y`. -/
theorem existsUnique_hom_of_spacesBaseChange_of_isIntegralHom (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (D : SpacesBaseChange B S hS f)
    (V' V : SpacesEtale B S hS Y) (d : (D.functor.obj V').1.left.obj ⟶ V.1.left.obj)
    (hd : d ≫ V.1.hom.hom = (D.projection.app V').hom ≫ V'.1.hom.hom) :
    ∃! a : V'.1.left.obj ⟶ V.1.left.obj,
      (D.projection.app V').hom ≫ a = d ∧ a ≫ V.1.hom.hom = V'.1.hom.hom := by
  obtain ⟨hgint, hgui, hgs⟩ :=
    isIntegralHom_universallyInjective_isSurjective_projection B S hS f hint hui hsurj D V'
  obtain ⟨a, hga, hav⟩ :=
    exists_hom_of_section_descent B S hS Y.property V'.1.left.property
      (D.functor.obj V').1.left.property V.1.left.property V.property hgint hgui hgs d hd
  exact ⟨a, ⟨hga, hav⟩, fun b ⟨hb1, hb2⟩ ↦ eq_of_isSurjective_of_isEtale B S hS Y.property
    V.1.left.property V'.1.left.property (D.functor.obj V').1.left.property V.1.hom.hom V.property
    (hb2.trans hav.symm) hgs (hb1.trans hga.symm)⟩

/-! ### Fullness and full faithfulness -/

/-- Every morphism of base changes is the base change of a morphism of the spaces-étale site of
`Y`. -/
private theorem exists_map_eq_spacesBaseChange_of_isIntegralHom (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (D : SpacesBaseChange B S hS f)
    (V' V : SpacesEtale B S hS Y) (c : D.functor.obj V' ⟶ D.functor.obj V) :
    ∃ a : V' ⟶ V, D.functor.map a = c := by
  have hcX : c.hom.left ≫ (D.functor.obj V).1.hom = (D.functor.obj V').1.hom := Over.w c.hom
  have hAS : (c.hom.left ≫ D.projection.app V) ≫ V.1.hom
      = D.projection.app V' ≫ V'.1.hom := by
    rw [Category.assoc, (D.isPullback V).w, ← Category.assoc, hcX, (D.isPullback V').w]
  obtain ⟨a, ⟨ha1, ha2⟩, -⟩ :=
    existsUnique_hom_of_spacesBaseChange_of_isIntegralHom B S hS f hint hui hsurj D V' V
      (c.hom.left ≫ D.projection.app V).hom (congrArg (fun k ↦ k.hom) hAS)
  have hα : (ObjectProperty.homMk a : V'.1.left ⟶ V.1.left) ≫ V.1.hom = V'.1.hom :=
    ObjectProperty.hom_ext _ ha2
  let a' : V' ⟶ V := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα)
  refine ⟨a', ObjectProperty.hom_ext _ (Over.OverMorphism.ext ((D.isPullback V).hom_ext ?_ ?_))⟩
  · exact (D.projection.naturality a').trans (ObjectProperty.hom_ext _ ha1)
  · exact (Over.w (D.functor.map a').hom).trans hcX.symm

/-- Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism of algebraic
spaces over `S`. The base-change functor `V ↦ V_X = X ×_Y V` from the spaces-étale site of `Y` to
that of `X` is full. -/
theorem full_spacesBaseChange_of_isIntegralHom_of_universallyInjective (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.Full where
  map_surjective {V' V} c :=
    exists_map_eq_spacesBaseChange_of_isIntegralHom B S hS f hint hui hsurj
      (spacesBaseChange B S hS f) V' V c

/-- Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism of algebraic
spaces over `S`. The base-change functor `V ↦ V_X = X ×_Y V` from the spaces-étale site of `Y` to
that of `X` is fully faithful. -/
noncomputable def fullyFaithfulSpacesBaseChangeOfIsIntegralHomOfUniversallyInjective
    (f : X ⟶ Y) (hint : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.FullyFaithful :=
  letI := full_spacesBaseChange_of_isIntegralHom_of_universallyInjective B S hS f hint hui hsurj
  letI := faithful_spacesBaseChange_of_isIntegralHom_of_universallyInjective B S hS f hint hui
    hsurj
  Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.Space

end
