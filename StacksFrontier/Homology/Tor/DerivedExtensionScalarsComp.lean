module

public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Derived extension of scalars along a composite of ring homomorphisms

Let `f : R →+* S` and `g : S →+* T` be homomorphisms of commutative rings.  Derived extension of
scalars along `f`, followed by derived extension of scalars along `g`, is derived extension of
scalars along `g ∘ f`.  Both composites are total left derived functors of degreewise extension
of scalars along `g ∘ f`: a K-flat complex computes either one, and degreewise extension of
scalars along `f` carries K-flat complexes to K-flat complexes (Stacks 06Y1), so the comparison
produced by the universal property of the right-hand side is invertible.

What is recorded here is not only the isomorphism but the equation it satisfies against the three
comparisons — `derivedExtensionScalarsCompIso_hom_app_comp_comparison`.  Without that equation the
isomorphism is opaque to a diagram chase, which is the only use it has: the derived stalk of a
composite of derived pullbacks is computed by iterating the stalk formula, and the ring-level step
of that iteration is exactly this composite.

## Main definitions

* `StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIso`: the composition
  isomorphism for *degreewise* extension of scalars, read in the derived category.
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompComparison`: the comparison
  from the composite of the two derived functors to degreewise extension of scalars along `g ∘ f`.
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompHom`: the canonical morphism
  `T_f ⋙ T_g ⟶ T_{g ∘ f}` obtained from the universal property of `T_{g ∘ f}`.
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso`: the resulting natural
  isomorphism.

## Main results

* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompHom_fac`: the defining
  equation of the canonical morphism, from `CategoryTheory.Functor.leftDerived_fac_app`.
* `StacksDraft.DerivedExtensionScalarsComp.isIso_derivedExtensionScalarsCompHom`: the canonical
  morphism is invertible.
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_hom_app_comp_comparison`:
  **the characterizing equation**, at an arbitrary cochain complex.

## Implementation notes

*Why the isomorphism is produced from the universal property rather than by uniqueness of left
derived functors.*  `CategoryTheory.Functor.leftDerivedNatIso` would give the isomorphism directly
from an `IsLeftDerivedFunctor` instance on the composite, but establishing that instance means
establishing invertibility of the composite comparison on the K-flat class anyway, and the route
through `leftDerivedLift` keeps the characterizing equation as a `leftDerived_fac_app`, which is
the form a chase needs.

*Why invertibility is checked at an arbitrary object by transport.*  The comparison is invertible
at `Q.obj P` for K-flat `P` by the three `comparison_isIso_of_kFlat` fields; an arbitrary object
of the derived category receives a quasi-isomorphism from such a `Q.obj P` by Stacks 06YS, and
naturality transports invertibility along it.

## References

* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CochainComplex.DerivedExtensionScalars CochainComplex.KFlat

namespace StacksDraft.DerivedExtensionScalarsComp

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- **Degreewise extension of scalars composes.**  Extending scalars degreewise along `f` and
then along `g` is extending scalars degreewise along `g ∘ f`, read in the derived category.

This is `ModuleCat.extendScalarsComp` applied degreewise and localized. -/
def extensionScalarsComplexCompIso :
    (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplex.{u, u, u} g ≅
      extensionOfScalarsComplex.{u, u, u} (g.comp f) :=
  isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
      (ComplexShape.up ℤ)) DerivedCategory.Q

/-- The comparison from the composite of the two total derived extension-of-scalars functors to
degreewise extension of scalars along `g ∘ f`: the comparison for `f`, then the comparison for
`g`, then `extensionScalarsComplexCompIso`. -/
def derivedExtensionScalarsCompComparison :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor) ⟶
      extensionOfScalarsComplex.{u, u, u} (g.comp f) :=
  whiskerRight (totalDerivedExtensionScalars.{u, u, u} f).comparison
      (totalDerivedExtensionScalars.{u, u, u} g).functor ≫
    whiskerLeft ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
      (totalDerivedExtensionScalars.{u, u, u} g).comparison ≫
    (extensionScalarsComplexCompIso f g).hom

/-- The canonical morphism `T_f ⋙ T_g ⟶ T_{g ∘ f}`, from the universal property of the total
left derived functor on the right. -/
def derivedExtensionScalarsCompHom :
    (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor :=
  (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.leftDerivedLift
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    (derivedExtensionScalarsCompComparison f g)

/-- **The defining equation of the canonical morphism.**  Composing it with the comparison of
`T_{g ∘ f}` returns the composite comparison, at every cochain complex. -/
theorem derivedExtensionScalarsCompHom_fac (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsCompHom f g).app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P =
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (extensionScalarsComplexCompIso f g).hom.app P :=
  (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.leftDerived_fac_app
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    (derivedExtensionScalarsCompComparison f g) P

/-- **The canonical morphism is invertible**, so derived extension of scalars composes.  On a
K-flat complex all three comparisons are invertible, hence so is the canonical morphism there by
its defining equation; an arbitrary object receives a quasi-isomorphism from a K-flat complex, and
naturality transports invertibility along it. -/
instance isIso_derivedExtensionScalarsCompHom :
    IsIso (derivedExtensionScalarsCompHom f g) := by
  have key (X : DerivedCategory (ModuleCat.{u} R)) :
      IsIso ((derivedExtensionScalarsCompHom f g).app X) := by
    have hα (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
        IsIso ((derivedExtensionScalarsCompHom f g).app (DerivedCategory.Q.obj P)) := by
      have hD := (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison_isIso_of_kFlat P hP
      have hfP := (totalDerivedExtensionScalars.{u, u, u} f).comparison_isIso_of_kFlat P hP
      have hbase : ((CochainComplex.extendScalars f).obj P).KFlat := kFlat_baseChange f P hP
      have hgP := (totalDerivedExtensionScalars.{u, u, u} g).comparison_isIso_of_kFlat
        (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hbase
      have hm : IsIso ((totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P)) := inferInstance
      have he : IsIso ((extensionScalarsComplexCompIso f g).hom.app P) := inferInstance
      have h2 := IsIso.comp_isIso' hm (IsIso.comp_isIso' hgP he)
      rw [← derivedExtensionScalarsCompHom_fac] at h2
      exact (isIso_comp_right_iff
        ((derivedExtensionScalarsCompHom f g).app (DerivedCategory.Q.obj P))
        ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P)).mp h2
    let M := DerivedCategory.Q.objPreimage X
    obtain ⟨P, p, hP, -, hp, -⟩ := exists_kFlat_resolution.{u, u} M
    have := hp
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    have hn := (derivedExtensionScalarsCompHom f g).naturality e.hom
    have hiso : IsIso ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.map e.hom) :=
      ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.mapIso e).isIso_hom
    have h3 := IsIso.comp_isIso' (hα P hP) hiso
    rw [← hn] at h3
    exact (isIso_comp_left_iff _ _).mp h3
  exact NatIso.isIso_of_isIso_app _

/-- **Derived extension of scalars composes.**  `T_f ⋙ T_g ≅ T_{g ∘ f}`, by the canonical
morphism. -/
def derivedExtensionScalarsCompIso :
    (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor :=
  asIso (derivedExtensionScalarsCompHom f g)

/-- The underlying morphism of `derivedExtensionScalarsCompIso` is the canonical one. -/
@[simp]
theorem derivedExtensionScalarsCompIso_hom :
    (derivedExtensionScalarsCompIso f g).hom = derivedExtensionScalarsCompHom f g :=
  rfl

/-- **The characterizing equation of the composition isomorphism.**  At every cochain complex,
composing it with the comparison of `T_{g ∘ f}` returns the comparison for `f`, then the
comparison for `g`, then the degreewise composition isomorphism.  This is what makes the
isomorphism usable in a diagram chase. -/
theorem derivedExtensionScalarsCompIso_hom_app_comp_comparison
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsCompIso f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P =
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (extensionScalarsComplexCompIso f g).hom.app P :=
  derivedExtensionScalarsCompHom_fac f g P

/-- **The characterizing equation with the degreewise merge spelled out.**  The same equation as
`derivedExtensionScalarsCompIso_hom_app_comp_comparison`, with `extensionScalarsComplexCompIso`
replaced by `DerivedCategory.Q` of `CategoryTheory.Functor.mapHomologicalComplexCompIso` of
`ModuleCat.extendScalarsComp` — the spelling at which the comparison's target reads as
`(ModuleCat.extendScalars _).mapHomologicalComplex _ ⋙ DerivedCategory.Q` rather than as
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex`.

This is the only place the two spellings of degreewise extension of scalars followed by
localization meet.  A consumer that rewrote `extensionScalarsComplexCompIso` itself would ask the
elaborator to convert the two spellings inside whatever large term it is chasing; stated here, the
conversion is performed once, in this module, and every consumer sees only the spelling
`AlgebraicGeometry.germAlpha` and the degreewise merges are at. -/
theorem comparison_comp_comparison_comp_mapHomologicalComplexCompIso
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
            (ComplexShape.up ℤ)).hom.app P) =
      (derivedExtensionScalarsCompIso f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P :=
  (derivedExtensionScalarsCompIso_hom_app_comp_comparison f g P).symm

section Transport

variable {R₀ T₀ : Type u} [CommRing R₀] [CommRing T₀]

/-- **The comparison transported along an equation of ring homomorphisms.**  Two homomorphisms
`R₀ →+* T₀` that are equal carry the same comparison with degreewise extension of scalars: the
transport of the degreewise functor absorbs the transport of the derived one.

This is the companion of `comparison_comp_comparison_comp_mapHomologicalComplexCompIso` for the
*other* conversion a merge chase meets — the one between the comparison for a composite
`g ∘ f` of germ maps and the comparison for a homomorphism merely equal to it.  Like that lemma it
is stated here, where `Eq.subst` reduces it to reflexivity, so that no consumer has to convert. -/
theorem comparison_app_comp_Q_map_eqToHom (φ ψ : R₀ →+* T₀) (h : φ = ψ)
    (P : CochainComplex (ModuleCat.{u} R₀) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P ≫
        DerivedCategory.Q.map (eqToHom (congrArg
          (fun χ => ((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) h)) =
      eqToHom (congrArg
          (fun χ => (totalDerivedExtensionScalars.{u, u, u} χ).functor.obj
            (DerivedCategory.Q.obj P)) h) ≫
        (totalDerivedExtensionScalars.{u, u, u} ψ).comparison.app P := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P)

/-- **The derived functor transported along an equation of ring homomorphisms is natural.**  Two
homomorphisms `R₀ →+* T₀` that are equal carry the same derived extension of scalars, and the
transport between the two commutes with the functor's action on morphisms.

Stated here, where `Eq.subst` reduces it to reflexivity, so that a chase meeting the transport
between a composite of germ maps and a homomorphism merely equal to it does not have to convert. -/
theorem functor_map_comp_eqToHom (φ ψ : R₀ →+* T₀) (h : φ = ψ)
    {Y Y' : DerivedCategory (ModuleCat.{u} R₀)} (m : Y ⟶ Y') :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.map m ≫
        eqToHom (congrArg
          (fun χ => (totalDerivedExtensionScalars.{u, u, u} χ).functor.obj Y') h) =
      eqToHom (congrArg
          (fun χ => (totalDerivedExtensionScalars.{u, u, u} χ).functor.obj Y) h) ≫
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map m := by
  subst h
  simp

end Transport

end StacksDraft.DerivedExtensionScalarsComp

end
