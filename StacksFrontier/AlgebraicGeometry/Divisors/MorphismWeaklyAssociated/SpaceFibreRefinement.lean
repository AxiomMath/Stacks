module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFlatBaseChangeAscent
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance

/-!
# The fibre condition at a refinement of a field-valued point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `q` refine `p` as a
field-valued point of `Y`, that is, let `κ : q.siteObject ⟶ p.siteObject` carry the morphism
`p` presents to the morphism `q` presents. The fibre of `f` over `q` is then the base change of
the fibre of `f` over `p` along `κ`, and `κ` is a morphism of spectra of fields, hence flat and
surjective. So the fibre condition of Stacks 0CUZ at `p` implies the fibre condition at `q`:
the witness on the fibre over `p` is carried to a witness on the fibre over `q` by
`AlgebraicGeometry.Space.exists_isWeaklyAssociatedPoint_modulePullback_of_isPullback_yoneda`.

Every point of `Y'` above the class of `p` is, moreover, the class of such a refinement: a
field-valued representative of a point of the fibre of `g : Y' ⟶ Y` over `p` above it presents
one, the morphism `κ` being the second projection of that fibre read through Yoneda.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedOnFibre_of_refines`: the fibre condition at a
  refinement of a field-valued point.
* `AlgebraicGeometry.Space.exists_fieldValuedPoint_refining`: a point of `Y'` above the class of
  `p` is the class of a field-valued point refining `p` through `g`.

## Implementation notes

The refinement is recorded as a morphism of the objects of the site the two points are defined
on together with the identity of the presented morphisms, rather than as
`AlgebraicGeometry.Space.FieldValuedPoint.Dominates`, because that identity is what the
cartesian square comparing the two fibres is built from.

Flatness of the morphism of field spectra is flatness over a field, and its surjectivity is the
surjectivity of any morphism onto a one-point space from a nonempty one; the spectrum of the
field of definition of a field-valued point is the underlying scheme of its object of the site,
on the nose.

The module universe is that of the structure rings, since Stacks 0CUU is available there.

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of the spectra of the fields of definition -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism between the objects of the site two field-valued points are defined on is flat:
it is a morphism of schemes over the spectrum of a field. -/
theorem flat_toScheme_map_siteObject {p q : FieldValuedPoint B S hS F}
    (κ : q.siteObject ⟶ p.siteObject) :
    Flat ((BigFppfOver.toScheme B S hS).map κ) := by
  have h : Flat (show Spec (CommRingCat.of q.carrier) ⟶ Spec (CommRingCat.of p.carrier) from
    (BigFppfOver.toScheme B S hS).map κ) := inferInstance
  exact h

/-- A morphism between the objects of the site two field-valued points are defined on is
surjective: the spectrum of a field is a one-point space and the spectrum of a field is
nonempty. -/
theorem surjective_toScheme_map_siteObject {p q : FieldValuedPoint B S hS F}
    (κ : q.siteObject ⟶ p.siteObject) :
    Surjective ((BigFppfOver.toScheme B S hS).map κ) := by
  have := subsingleton_toScheme_siteObject B S hS F p
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj q.siteObject) := by
    show Nonempty ↥(Spec (CommRingCat.of q.carrier))
    infer_instance
  exact ⟨fun _ ↦ ⟨hne.some, Subsingleton.elim _ _⟩⟩

/-! ### The fibre over a refinement -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The fibre of `f` over a refinement of a field-valued point is the base change of the
fibre over that point.** The comparison morphism of fibres is compatible with the projections
to the source of `f`, and the square it sits in over `κ` is cartesian: the square cutting out
the fibre over `q` is the composite of it with the square cutting out the fibre over `p`. -/
theorem exists_fibreMap_isPullback_of_refines (f : X ⟶ Y)
    {p q : FieldValuedPoint B S hS Y.1} (κ : q.siteObject ⟶ p.siteObject)
    (hκ : yoneda.map κ ≫ fieldMorphism B S hS Y.1 p = fieldMorphism B S hS Y.1 q) :
    ∃ π : fibreAtFieldValuedPoint B S hS f q ⟶ fibreAtFieldValuedPoint B S hS f p,
      π ≫ fibreAtFieldValuedPointProjection B S hS f p =
          fibreAtFieldValuedPointProjection B S hS f q ∧
        IsPullback π.hom (pullback.snd f.hom (fieldMorphism B S hS Y.1 q))
          (pullback.snd f.hom (fieldMorphism B S hS Y.1 p)) (yoneda.map κ) := by
  have hcond : pullback.fst f.hom (fieldMorphism B S hS Y.1 q) ≫ f.hom =
      (pullback.snd f.hom (fieldMorphism B S hS Y.1 q) ≫ yoneda.map κ) ≫
        fieldMorphism B S hS Y.1 p := by
    rw [Category.assoc, hκ]
    exact pullback.condition
  have hlift : (ObjectProperty.homMk (pullback.lift _ _ hcond) :
        fibreAtFieldValuedPoint B S hS f q ⟶ fibreAtFieldValuedPoint B S hS f p).hom ≫
      pullback.fst f.hom (fieldMorphism B S hS Y.1 p) =
      pullback.fst f.hom (fieldMorphism B S hS Y.1 q) := pullback.lift_fst _ _ _
  refine ⟨ObjectProperty.homMk (pullback.lift _ _ hcond),
    (ObjectProperty.fullyFaithfulι _).map_injective hlift, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f.hom (fieldMorphism B S hS Y.1 p))
  rw [hlift, hκ]
  exact IsPullback.of_hasPullback f.hom (fieldMorphism B S hS Y.1 q)

/-- **The fibre condition of Stacks 0CUZ passes to a refinement of the field-valued point.**
If some point of the fibre of `f` over `p` above `x` is weakly associated to the restriction of
a quasi-coherent module `F`, then so is some point of the fibre over any refinement `q` of `p`.

The fibre over `q` is the base change of the fibre over `p` along the morphism of field spectra
underlying the refinement, which is flat and surjective. -/
theorem isWeaklyAssociatedOnFibre_of_refines (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) {p q : FieldValuedPoint B S hS Y.1}
    (κ : q.siteObject ⟶ p.siteObject)
    (hκ : yoneda.map κ ≫ fieldMorphism B S hS Y.1 p = fieldMorphism B S hS Y.1 q)
    {x : points B S hS X.1} (h : IsWeaklyAssociatedOnFibre B S hS f F p x) :
    IsWeaklyAssociatedOnFibre B S hS f F q x := by
  obtain ⟨θ, hθ, hwa⟩ := h
  obtain ⟨π, hπproj, sqπ⟩ := exists_fibreMap_isPullback_of_refines B S hS f κ hκ
  obtain ⟨θ', hθ'π, hwa'⟩ := exists_isWeaklyAssociatedPoint_modulePullback_of_isPullback_yoneda
    B S hS (pullback.snd f.hom (fieldMorphism B S hS Y.1 p))
    (pullback.snd f.hom (fieldMorphism B S hS Y.1 q)) π κ sqπ
    (flat_toScheme_map_siteObject B S hS κ) (surjective_toScheme_map_siteObject B S hS κ)
    ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (fibreAtFieldValuedPointProjection B S hS f p) F hF) hwa
  refine ⟨θ', ?_, ?_⟩
  · have hhom : π.hom ≫ (fibreAtFieldValuedPointProjection B S hS f p).hom =
        (fibreAtFieldValuedPointProjection B S hS f q).hom :=
      congrArg (fun m : fibreAtFieldValuedPoint B S hS f q ⟶ X ↦ m.hom) hπproj
    have hpt := congrArg
      (fun k ↦ pointsMap B S hS (fibreAtFieldValuedPoint B S hS f q).1 k θ') hhom
    simp only [pointsMap_comp, Function.comp_apply] at hpt
    rw [← hpt, hθ'π, hθ]
  · refine (isWeaklyAssociatedPoint_congr B S hS
      ((modulePullbackCompIso B S hS π (fibreAtFieldValuedPointProjection B S hS f p)).app F ≪≫
        eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj F) hπproj)) θ').1 hwa'

/-! ### Refinements through a morphism of the target -/

variable {Y' : AlgebraicSpaces B S hS}

/-- **A point of `Y'` above the class of `p` is the class of a field-valued point refining `p`
through `g`.** A field-valued representative of a point of the fibre of `g` over `p` above the
given point presents such a refinement, the morphism of field spectra being the second
projection of that fibre read through Yoneda. -/
theorem exists_fieldValuedPoint_refining (g : Y' ⟶ Y) (p : FieldValuedPoint B S hS Y.1)
    {y' : points B S hS Y'.1}
    (hy' : p.class B S hS Y.1 = pointsMap B S hS Y'.1 g.hom y') :
    ∃ (q : FieldValuedPoint B S hS Y'.1) (κ : q.siteObject ⟶ p.siteObject),
      q.class B S hS Y'.1 = y' ∧
        yoneda.map κ ≫ fieldMorphism B S hS Y.1 p =
          fieldMorphism B S hS Y.1 (FieldValuedPoint.map B S hS Y'.1 g.hom q) := by
  obtain ⟨η, hη⟩ := exists_point_fibre_of_pointsMap_eq_class B S hS g hy'
  obtain ⟨ρ, hρ⟩ := Quot.exists_rep η
  refine ⟨FieldValuedPoint.map B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p))
      (pullback.fst g.hom (fieldMorphism B S hS Y.1 p)) ρ,
    (FieldValuedPoint.map B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p))
      (pullback.snd g.hom (fieldMorphism B S hS Y.1 p)) ρ).siteHom, ?_, ?_⟩
  · rw [← pointsMap_class]
    show pointsMap B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p))
      (fibreAtFieldValuedPointProjection B S hS g p).hom (Quot.mk _ ρ) = y'
    rw [hρ]
    exact hη
  · have hsnd : yoneda.map (FieldValuedPoint.map B S hS
          (pullback g.hom (fieldMorphism B S hS Y.1 p))
          (pullback.snd g.hom (fieldMorphism B S hS Y.1 p)) ρ).siteHom =
        fieldMorphism B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p)) ρ ≫
          pullback.snd g.hom (fieldMorphism B S hS Y.1 p) :=
      (fieldMorphism_yoneda B S hS _).symm.trans
        (fieldMorphism_map B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p)) _ ρ)
    have hfst : fieldMorphism B S hS Y.1 (FieldValuedPoint.map B S hS Y'.1 g.hom
          (FieldValuedPoint.map B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p))
            (pullback.fst g.hom (fieldMorphism B S hS Y.1 p)) ρ)) =
        (fieldMorphism B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p)) ρ ≫
          pullback.fst g.hom (fieldMorphism B S hS Y.1 p)) ≫ g.hom :=
      (fieldMorphism_map B S hS Y'.1 g.hom _).trans
        (congrArg (· ≫ g.hom)
          (fieldMorphism_map B S hS (pullback g.hom (fieldMorphism B S hS Y.1 p)) _ ρ))
    refine Eq.trans (congrArg (· ≫ fieldMorphism B S hS Y.1 p) hsnd) ?_
    rw [hfst]
    simp only [Category.assoc]
    rw [pullback.condition]
    exact Category.assoc _ _ _

end AlgebraicGeometry.Space

end
