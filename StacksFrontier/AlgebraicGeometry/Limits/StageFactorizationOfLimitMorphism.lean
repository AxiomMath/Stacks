module

public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.CategoryTheory.Limits.ConeInOverOfCone

/-!
# A morphism out of a cofiltered limit of affine schemes factors through a stage

Let `D : I ⥤ Scheme` be a cofiltered diagram of affine schemes equipped with a compatible family
of morphisms `p i : D.obj i ⟶ S`, and let `c` be a limit cone whose vertex carries the morphism
`m : c.pt ⟶ S` induced by that family. A morphism `g : c.pt ⟶ T` over `S`, with `T ⟶ S` locally
of finite presentation, factors as `c.π.app i ≫ gᵢ` for some stage `i`, with `gᵢ` again a
morphism over `S`.

This is the shape in which Tag 01ZC is used when the limit is a presentation of the spectrum of a
completed local ring and `T` is a scheme of finite type over the base.

## Main results

* `AlgebraicGeometry.exists_stage_comp_eq_of_locallyOfFinitePresentation`: the factorization.

## Implementation notes

Tag 01ZC is formalized as
`AlgebraicGeometry.Scheme.locallyOfFinitePresentation_iff_isLimitPreserving_yoneda`, whose
consequence `AlgebraicGeometry.Scheme.exists_comp_eq_of_isLimitPreserving` takes a limit cone in
the over category `Over S`. The diagram and the cone here live in `Scheme`, with the structure
morphisms given as a natural transformation to a constant functor; `CategoryTheory.Functor.toOver`
and `CategoryTheory.Limits.IsLimit.inOver` transport them to `Over S`.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The structure morphisms of a diagram given as a natural transformation to a constant functor
are compatible with the transition morphisms. -/
theorem map_comp_natTrans_app {I : Type u} [Category.{u} I] {S : Scheme.{u}}
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S) {i j : I} (e : i ⟶ j) :
    D.map e ≫ p.app j = p.app i := by
  simp

/-- **A morphism out of a cofiltered limit of affine schemes over `S` into a scheme locally of
finite presentation over `S` factors through a stage**, by a morphism which is again a morphism
over `S`. -/
theorem exists_stage_comp_eq_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (haff : ∀ i, IsAffine (D.obj i))
    {T : Scheme.{u}} (q : T ⟶ S) [LocallyOfFinitePresentation q]
    (g : c.pt ⟶ T) (hg : g ≫ q = m) :
    ∃ (i : I) (gi : D.obj i ⟶ T), gi ≫ q = p.app i ∧ c.π.app i ≫ gi = g := by
  have hf : ∀ {i j : I} (e : i ⟶ j), D.map e ≫ p.app j = p.app i :=
    fun {_ _} e => map_comp_natTrans_app D p e
  have : Nonempty I := IsCofiltered.nonempty
  have : LocallyOfFinitePresentation (Over.mk q).hom := ‹LocallyOfFinitePresentation q›
  have H : Scheme.IsLimitPreserving S (yoneda.obj (Over.mk q)) :=
    Scheme.isLimitPreserving_yoneda_of_locallyOfFinitePresentation (Over.mk q)
  obtain ⟨i, gi, hgi⟩ := Scheme.exists_comp_eq_of_isLimitPreserving H
    (D.toOver S p.app hf) (Cone.inOver p.app hf c m hm)
    (IsLimit.inOver p.app hf hc m hm) (fun i => haff i)
    (Over.homMk g hg)
  exact ⟨i, gi.left, Over.w gi, congrArg Over.Hom.left hgi⟩

end AlgebraicGeometry

end
