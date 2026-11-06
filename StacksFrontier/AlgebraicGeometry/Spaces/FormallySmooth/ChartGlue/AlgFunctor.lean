module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.SpecSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Transport

/-!
# The functor of lifts of a lifting problem, on algebras

Let `f : X ⟶ Y` be a transformation of presheaves on the big fppf site over `S`, let `T'` be an
affine object with ring of global sections `A'`, and let `y` be a section of `Y` over `T'`. For a
class `P` of `A'`-algebras whose spectra belong to the site, the sections of `X` over `Spec C`
lying over the restriction of `y` form a functor on `P`. It is the functor on which the gluing of
`Stacks.ChartGlue` operates.

## Main definitions

* `AlgebraicGeometry.Space.ChartGlue.specP`: the spectrum of an algebra of `P`, as an object of
  the site.
* `AlgebraicGeometry.Space.ChartGlue.algFunctor`: the functor `C ↦ {g ∈ X(Spec C) | f g = y}`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  (P : ObjectProperty (CommAlgCat.{u} (ringOf B S hS T')))
  (hP : ∀ C : P.FullSubcategory, B.Contains (Spec (CommRingCat.of C.obj)))

/-- The spectrum of an algebra of `P`, as an object of the site. -/
abbrev specP (C : P.FullSubcategory) : BigFppfOver B S hS := specObj B S hS T' C.obj (hP C)

/-- The morphism of spectra of a morphism of `P`. -/
abbrev specPMap {C D : P.FullSubcategory} (h : C ⟶ D) :
    specP B S hS T' P hP D ⟶ specP B S hS T' P hP C :=
  specMap B S hS T' (hP C) (hP D) h.hom.hom

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (y : Y.obj (op T'))

/-- **The functor of points over `y`**: `C ↦ {g ∈ X(Spec C) | f g = y|_{Spec C}}`. -/
def algFunctor : P.FullSubcategory ⥤ Type u where
  obj C := {g : X.obj (op (specP B S hS T' P hP C)) //
    f.app _ g = Y.map (specToT B S hS T' C.obj (hP C)).op y}
  map {C D} h := TypeCat.ofHom fun g ↦ ⟨X.map (specPMap B S hS T' P hP h).op g.1, by
    rw [f.naturality_apply (specPMap B S hS T' P hP h).op g.1, g.2,
      ← Functor.map_comp_apply, ← op_comp, specMap_specToT]⟩
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change X.map (specMap B S hS T' (hP C) (hP C) (AlgHom.id _ _)).op g.1 = g.1
    rw [specMap_id, op_id, Functor.map_id_apply]
  map_comp {C D E} h k := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change X.map (specMap B S hS T' (hP C) (hP E) (k.hom.hom.comp h.hom.hom)).op g.1 =
      X.map (specMap B S hS T' (hP D) (hP E) k.hom.hom).op
        (X.map (specMap B S hS T' (hP C) (hP D) h.hom.hom).op g.1)
    rw [specMap_comp B S hS T' (hP C) (hP D) (hP E), op_comp, Functor.map_comp_apply]

end AlgebraicGeometry.Space.ChartGlue

end
