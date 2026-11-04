module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointsAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The étale chart of a relative Proj over an atlas of its base

Let `π : P ⟶ X` be presented as a relative homogeneous spectrum over the scheme points of `X`
(`AlgebraicGeometry.Space.RelativeProjPoints`, the second assertion of Stacks 084B), and let
`u : U ⟶ X` be a scheme atlas of `X`, surjective and étale after every representable base change.
The base change `P_U = U ×_X P` is the object `d.fibre U u` of the site, and its morphism
`d.fibreToSpace U u : P_U ⟶ P` is the base change of `u` along `π`.  The descent of Stacks 084D
takes place along that morphism, and this file records the two facts about it that the descent
consumes.

* It is an étale covering of `P`: étale and surjective after every representable base change,
  both being stable under base change, so `AlgebraicGeometry.Space.isEtaleCovering_atlas` applies.
* The comparison morphisms of the third assertion of Stacks 084B compose: the comparison along a
  composite `h' ≫ h` of test objects is the composite of the comparisons, up to the identification
  of the two spellings `yoneda.map (h' ≫ h) ≫ f` and `yoneda.map h' ≫ (yoneda.map h ≫ f)` of the
  point.  This is what makes the comparison isomorphisms of twists along these morphisms a cocycle.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.isEtale_fibreToSpace`,
  `…surjective_fibreToSpace`, `…etale_fibreToSpace` and `…isEtaleCovering_fibreToSpace`: the
  chart `P_U ⟶ P` over an atlas of `X` is étale, surjective and étale after representable base
  change, and an étale covering of `P`.
* `AlgebraicGeometry.Space.RelativeProjPoints.fibreComparison_comp`: the comparison morphisms
  compose.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
  (d : RelativeProjPoints B S hS π)

/-! ### The chart over an atlas of the base -/

/-- **The base change of an étale morphism to `X` along `π` is étale.** -/
theorem isEtale_fibreToSpace {U : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    (hu : IsEtale B S hS u) : IsEtale B S hS (d.fibreToSpace U u) :=
  isEtale_of_isPullback_yoneda B S hS (d.isPullback U u).flip hu

/-- **The base change of a morphism surjective after representable base change is surjective
after representable base change.** -/
theorem surjective_fibreToSpace {U : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    (hu : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (d.fibreToSpace U u) :=
  presheaf_of_isPullback B S hS (d.isPullback U u).flip hu

/-- **The base change of a morphism étale after representable base change is étale after
representable base change.** -/
theorem etale_fibreToSpace {U : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    (hu : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (d.fibreToSpace U u) :=
  presheaf_of_isPullback B S hS (d.isPullback U u).flip hu

/-- **The chart `P_U ⟶ P` over a scheme atlas `U ⟶ X` is an étale covering of `P`**, as a family
indexed by a one-element type. -/
theorem isEtaleCovering_fibreToSpace (hP : IsAlgebraicSpace B S hS P)
    {U : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u)
    (het : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u) :
    IsEtaleCovering B S hS (fun _ : PUnit.{u + 1} => yoneda.obj (d.fibre U u))
      (fun _ => d.fibreToSpace U u) :=
  isEtaleCovering_atlas B S hS hP (d.surjective_fibreToSpace hsurj) (d.etale_fibreToSpace het)

/-! ### The comparison morphisms compose -/

/-- Reading the morphism to `P` across an equality of points. -/
theorem map_eqToHom_fibreToSpace {T : BigFppfOver B S hS} {p p' : yoneda.obj T ⟶ X}
    (e : p = p') :
    yoneda.map (eqToHom (congrArg (d.fibre T) e)) ≫ d.fibreToSpace T p' = d.fibreToSpace T p := by
  subst e
  simp

/-- Reading the structure morphism across an equality of points. -/
theorem eqToHom_comp_fibreHom {T : BigFppfOver B S hS} {p p' : yoneda.obj T ⟶ X}
    (e : p = p') :
    eqToHom (congrArg (d.fibre T) e) ≫ d.fibreHom T p' = d.fibreHom T p := by
  subst e
  simp

/-- **The comparison morphisms of the third assertion of Stacks 084B compose.**  For
`h' : T'' ⟶ T'` and `h : T' ⟶ T`, the comparison `T'' ×_X P ⟶ T ×_X P` along `h' ≫ h` is the
comparison along `h'` followed by the comparison along `h`, after identifying the two spellings of
the point `T'' ⟶ X`. -/
theorem fibreComparison_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' T'' : BigFppfOver B S hS} (h : T' ⟶ T) (h' : T'' ⟶ T') :
    d.fibreComparison T f (h' ≫ h) =
      eqToHom (congrArg (d.fibre T'') (by rw [Functor.map_comp, Category.assoc])) ≫
        d.fibreComparison T' (yoneda.map h ≫ f) h' ≫ d.fibreComparison T f h := by
  apply Yoneda.fullyFaithful.map_injective
  refine (d.isPullback T f).hom_ext ?_ ?_
  · refine (d.map_fibreComparison_comp_fibreToSpace T f (h' ≫ h)).trans ?_
    rw [yoneda.map_comp (eqToHom _) _,
      yoneda.map_comp (d.fibreComparison T' (yoneda.map h ≫ f) h'), Category.assoc,
      Category.assoc, map_fibreComparison_comp_fibreToSpace,
      map_fibreComparison_comp_fibreToSpace, map_eqToHom_fibreToSpace]
    rw [Functor.map_comp, Category.assoc]
  · rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [fibreComparison_comp_fibreHom, Category.assoc, Category.assoc,
      fibreComparison_comp_fibreHom,
      ← Category.assoc (d.fibreComparison T' (yoneda.map h ≫ f) h'),
      fibreComparison_comp_fibreHom,
      ← eqToHom_comp_fibreHom d (show yoneda.map (h' ≫ h) ≫ f =
        yoneda.map h' ≫ yoneda.map h ≫ f by rw [Functor.map_comp, Category.assoc])]
    simp only [Category.assoc]

end RelativeProjPoints

end AlgebraicGeometry.Space

end
